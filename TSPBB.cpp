/////////////////////////////////////////////////////////////
//BACKTRACKING y BRANCH AND BOUND                           //
//Problema: TSP                                            //                                               
//                                                         //
// Para la ejecución una vez compilado:                    //
// ./TSP "k" "l                                            //
// Siendo k -> datos de prueba (ulysses16, att48...)       //
// Siendo l -> algoritmo(1->cercania, 2->insercion, 3->2-opt)
/////////////////////////////////////////////////////////////

#include <iostream>
#include <ctime>
#include <cmath>
#include <cstdlib>
#include <cassert>
#include <cstring>
#include <chrono>
#include <fstream>
#include <vector>
#include <time.h>
#include <queue>

using namespace std;
using namespace std::chrono;

//Para tomar los tiempos
high_resolution_clock::time_point tantes, tdespues;
duration<double> transcurrido;

const int MAX=280;

//Estructura de una coordenada
struct coord{
    double x;
    double y;
};

void generarCiudades(coord ciudades[], int n, double max_distancia = 50.0)
{
    for (int i = 0; i < n; i++)
    {
        double min = -50.0;
        double max = 50.0;
        ciudades[i].x = min + static_cast <double> (rand()) /( static_cast <double> (RAND_MAX/(max-min)));
        ciudades[i].y = min + static_cast <double> (rand()) /( static_cast <double> (RAND_MAX/(max-min)));
    }
}

//Función que nos calcula la distancia entre dos ciudades
static int calcularDistancia(coord ciudad1, coord ciudad2){
    float dx, dy;
    dx=ciudad2.x-ciudad1.x;
    dy=ciudad2.y-ciudad1.y;
    dx=dx*dx;
    dy=dy*dy;
    float d=sqrt(dx+dy);

    //Esto lo hacemos para reondear la distancia que nos salga
    int aux=d;
    d=d-aux;
    if(d>=0.5) aux++;
    if(aux==0) aux=1;
    return aux;
}

//Función que calcula la suma total del camino
static int distanciaTotal(vector<int> camino, int matriz[MAX][MAX]){
  int longi=0;
  for(int i=0;i<camino.size()-1;++i){
      longi+=matriz[camino[i]][camino[i+1]];
  }
  longi+=matriz[camino[camino.size()-1]][camino[0]];
  return longi;
}

struct Nodo{
    int nivel;
    vector<int> camino;             //Solución parcial
    double cota_local;
    vector<int> ciudadesNoElegidas; 
};

class comparaNodos{
public:
    bool operator()(const Nodo & n1, const Nodo & n2){
        return n1.cota_local > n2.cota_local;
    }
};


//ALGORITMO DE CERCANIA (Lo utilizamos para calcular la cota global)
int cotaGlobal(vector<int> &ciu, int matriz[MAX][MAX]){

    vector<int> res;
    int num_ciudades = ciu.size();
    int ciudades=ciu.size()-1;
    int ciudad, min;
    bool utilizados[num_ciudades];

    //Inicializa todas las ciudades a false para indicar que no se han visitado
    for(int i = 0; i < num_ciudades; ++i){
        utilizados[i] = false;
    }

    //Metemos la primera ciudad
    res.push_back(0);

    int c_actual = 0;

    while(ciudades != 0){
        
        min = 0;
        
        for(int j = 0; j < num_ciudades; ++j){
            //Cada vez que comprobamos la siguiente ciudad con distancia mínima, calculamos el primer min
            if(min == 0 && c_actual!=j && utilizados[j]!=true){
                min = matriz[c_actual][j];
                ciudad = j;

            //Cuando hemos calculado el primer minimo, comprobamos las siguientes ciudades
            }else if(c_actual!=j && matriz[c_actual][j] < min && utilizados[j]!=true){
                min = matriz[c_actual][j];
                ciudad = j;
            }
        }

        //Aquí se marcan como visitadas ya estas ciudades para que no se vuelvan a comparar
        utilizados[c_actual] = true;
        utilizados[ciudad] = true;

        //Añadimos la ciudad nás próxima
        res.push_back(ciudad);

        c_actual = ciudad;
        //Decrementamos el numero de ciudades para comprobar las que nos queden sin visitar
        ciudades--;
    }

    return distanciaTotal(res,matriz);
}


//Función que calcula la cota local de un nodo
void cotaLocal(Nodo & nodo, int matriz[MAX][MAX], int num_ciudades){

    int cota = 0;
    int min;

    //Calcula el coste del camino ya acumulado
    for(int i = 0; i<nodo.nivel; ++i)
        cota += matriz[nodo.camino[i]][nodo.camino[i+1]];

    //Calcula la suma de las aristas minimas
    for(int i = 0; i<nodo.ciudadesNoElegidas.size(); ++i){
        min = numeric_limits<int>::max();
        for(int j = 1; j<num_ciudades+1; ++j)
        if(nodo.ciudadesNoElegidas[i] != j && matriz[nodo.ciudadesNoElegidas[i]][j] < min)
            min = matriz[nodo.ciudadesNoElegidas[i]][j];
        cota += min;
    }

    //Añadir el mínimo recorrido para salir de la última ciudad elegida
    min = numeric_limits<int>::max();
    for(int i = 1; i<num_ciudades+1; ++i)
        if(i != nodo.camino[nodo.nivel] && matriz[i][nodo.camino[nodo.nivel]] < min)
        min = matriz[i][nodo.camino[nodo.nivel]];
    cota += min;

    nodo.cota_local = cota;
}


//Función que crea la raiz del árbol
Nodo Raiz(int num_ciudades, int matriz[MAX][MAX]){
    Nodo nodo;
    nodo.nivel = 0;
    nodo.camino.resize(num_ciudades);

    //comenzamos con la primera ciudad
    nodo.camino[nodo.nivel] = 1; 
    for(int i = 2; i<=num_ciudades; ++i){
        nodo.ciudadesNoElegidas.push_back(i);
    }

    cotaLocal(nodo, matriz, num_ciudades);

    return nodo;
}


//Función que crea el hijo de un nodo
Nodo generaHijo(const Nodo &padre, int ciudad, int num_ciudades, int matriz[MAX][MAX]){
    Nodo hijo = padre;
    hijo.nivel = padre.nivel + 1;
    hijo.camino[hijo.nivel] = ciudad;
    bool encontrado = false;

    //Bucle para eliminar el hijo de la lista de ciudades no elegidas
    for(auto it = hijo.ciudadesNoElegidas.begin(); it != hijo.ciudadesNoElegidas.end() && !encontrado; ++it){
        if(*it == ciudad){
        encontrado = true;
        hijo.ciudadesNoElegidas.erase(it);
        }
    }
    cotaLocal(hijo, matriz, num_ciudades);
    return hijo;
}


//ALGORITMO BRANCH AND BOUND
Nodo tspBB(int num_ciudades, int matriz[MAX][MAX], vector<int> &ciudades){

    int ciudad, nodos_expandidos = 0, num_podas = 0;

    int tam_max = numeric_limits<int>::min();

    int distancia = 0;

    Nodo nodoActual, hijo, mejorNodo;
    priority_queue<Nodo, vector<Nodo>, comparaNodos> cola;
    int CG = cotaGlobal(ciudades, matriz);

    nodoActual = Raiz(num_ciudades, matriz);
    cola.push(nodoActual);

    while(!cola.empty() && (cola.top().cota_local < CG)){

        nodoActual = cola.top();
        cola.pop();
        nodos_expandidos++;

        for(int i = 0; i<nodoActual.ciudadesNoElegidas.size(); ++i){

        ciudad = nodoActual.ciudadesNoElegidas[i];
        hijo = generaHijo(nodoActual, ciudad, num_ciudades, matriz);

        if(hijo.nivel == num_ciudades-1){

            distancia = distanciaTotal(hijo.camino, matriz);
            if(distancia < CG){
            CG = distancia;
            mejorNodo = hijo;
            }

        }
        else if(hijo.cota_local < CG)
            cola.push(hijo);
        else
            num_podas++;
        if((int) cola.size() > tam_max) tam_max = (int) cola.size();
        }
    }
    //Imprimir resultados:
    cout << "Recorrido: ";
    for(int i = 0; i<mejorNodo.camino.size(); ++i)
        cout << "[" << mejorNodo.camino[i] << "]";
    cout << endl;
    cout << "Distancia: " << CG << endl;
    cout << "Nodos espandidos: " << nodos_expandidos << endl;
    cout << "Podas realizadas: " << num_podas << endl;
    cout << "Tamaño máximo de la cola: " << tam_max << endl;

    return mejorNodo;
}


int main(int argc, char *argv[]){
    
    srand(time(NULL));

    ifstream f;
    f.open(argv[2]);

    if (!f){
        cerr<<"No se pudo abrir el fichero "<<argv[1]<<endl;
        return -1;
    }

    int num_ciudades = atoi(argv[1]);

    int aux;
    coord ciudades[MAX];
    int matriz[MAX][MAX];

    //Leyendo coordenadas del fichero
    for(int i=0;i<num_ciudades;++i){
        f>>aux;
        f>>ciudades[i].x;
        f>>ciudades[i].y;
    }

    f.close();

    //Obtencion solucion optima del profesor
    // getline(f1,linea1);
    // getline(f1,linea1);
    // getline(f1,linea1);
    // getline(f1,linea1);
    // getline(f1,linea1);
    // vector<int> solucion_profe;

    // for(int i = 0; i < num_ciudades; ++i){
    //   f1 >> aux;
    //   solucion_profe.push_back(aux-1);
      
    // }

    // f1.close();

    //Rellenamos nuestra matriz de distancias
    for(int i = 0; i < num_ciudades; ++i){
        for(int j = 0; j < num_ciudades; ++j){
            matriz[i][j] = calcularDistancia(ciudades[i], ciudades[j]);   
        }
    }

    //Para mostra la matriz de distancias
    cout << "DISTANCIAS: " <<endl;
    for(int i = 0; i < num_ciudades; ++i){
        for(int j = 0; j < num_ciudades; ++j){
            cout << matriz[i][j] << " ";
        }
        cout << endl;
    }
    cout << endl;

    vector<int> cities;
	for(int i = 1; i<=num_ciudades; ++i)
		cities.push_back(i);

    ////////////////////////////// ALGORITMOS ///////////////////////////////////

    vector<int> res, auxiliar;
    auxiliar.push_back(0);

    tantes = high_resolution_clock::now();

    Nodo sol = tspBB(num_ciudades, matriz, cities);

    tdespues = high_resolution_clock::now();
    transcurrido = duration_cast<duration<double>>(tdespues - tantes);

    cout << "TIEMPO QUE TARDA EL ALGORITMO: " << transcurrido.count() << endl;

    ////////////////////////////////////////////////////////////////////////////
    // for(int i = 0; i < sol.camino.size(); ++i){
    //     cout << sol.camino[i]+1 << " ";
    // }
    // cout << endl;


    //CODIGO QUE CREA UN FICHERO DE SALIDA PARA PROBAR LOS DATOS OPTIMOS DEL PROFESOR EN GNUPLOT

    // cout << "Solucion final profesor: " << endl;
    // for(int i = 0; i < solucion_profe.size(); ++i){
    //     cout << solucion_profe[i]+1 << " ";
    // }
    // cout << endl;

    // cout << "Distancia total profesor: " << distanciaTotal(solucion_profe,matriz) << endl;

    //Fichero que contiene las ciudades creadas aleatoriamente


    //Fichero solución
    // ofstream fs("solucion.tsp");

    // for(int i = 0; i < num_ciudades; ++i){
    //   fs << " ";
    //   fs << res[i]+1 << " ";
    //   fs << ciudades[res[i]].x << " ";
    //   fs << ciudades[res[i]].y << " " << endl;
    // }

    // fs << " ";
    // fs << res[0]+1 << " ";
    // fs << ciudades[res[0]].x << " ";
    // fs << ciudades[res[0]].y << " " << endl;

    // fs << " " << "EOF";

    // fs.close();
}