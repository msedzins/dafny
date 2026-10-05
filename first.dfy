// Returns the nonnegative magnitude of an integer.
function abs(a: int): nat {
    if a >=0 then a else -a 
}

// Computes the greatest common divisor of two integers.
function gcd(a: int, b: int): nat
{   
    gcd_nat(abs(a), abs(b))
} 

// Computes the greatest common divisor of two natural numbers (>=0)
// Euclidean algorithm
function gcd_nat(a: nat, b: nat): nat
decreases b
{   
    if b == 0 then a
        else gcd_nat(b, a % b)
}

// Adding one modulus does not change the remainder.
lemma ModPlus(n: int, b: nat)
  requires b > 0
  ensures (n+b)%b == n%b
{
}

// Moves c toward zero to prove divisibility for either sign.
// This is obvious prove but not that obvious for Dafny apparently.
lemma ModExact(n: int, c: int, b: nat)
  requires b > 0 && n == b*c
  ensures n%b == 0
  decreases if c < 0 then -c else c
{
  if c > 0 {
    ModExact(b*(c-1), c-1, b);
    assert n == b*(c-1)+b;
    ModPlus(b*(c-1), b);
  } else if c < 0 {
    ModExact(b*(c+1), c+1, b);
    assert n+b == b*(c+1);
    ModPlus(n, b);
    assert (b*(c+1))%b == 0;
    assert (n+b)%b == 0;
    assert n%b == 0;
  } else {
    assert c == 0;
    assert n == 0;
    assert n%b == 0;
  }
}

// Returns a GCD and coefficients satisfying u*a + v*b == g.
// Extended Euclidean algorithm
method ExtendedEuclidean(a: nat, b:nat) returns (g: nat, u: int, v: int)
ensures g == gcd(a ,b)
ensures u*a + v*b == g
{

// With b = 0, a is the GCD and needs no second coefficient.
if b == 0 {
    g, u, v := a, 1, 0;
    return;
}

// (u,c) and (x,d) track each remainder as a combination of a and b.
var x: int, y: nat; 
g, y := a, b;
u, x := 1, 0;

ghost var c: int := 0;
ghost var d: int := 1;

// Each division step preserves the GCD and both linear combinations.
while y != 0 
invariant gcd(a,b) == gcd(g,y)
invariant g == a*u + b*c
invariant y == a*x + b*d
{
    var q: int := g / y;
    var t: int := g % y;    
    var s := u - q*x;

    
    u, g := x, y;
    x, y := s, t;
    c, d := d, c - q*d;

}

// g - a*u = b*c, so division by b gives the missing coefficient.
ModExact(g - a*u, c, b);
v := (g - a * u) / b;

} 

// Runs the extended Euclidean algorithm on a sample pair.
method Main() {
    var g, u, v := ExtendedEuclidean(10, 7);

    print "g=",g,"; u=", u,"; v=", v, ";\n";
}
