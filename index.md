The following are the theorems from [this list](http://www.cs.ru.nl/~freek/100/)
proved so far in the [Isabelle](https://isabelle.in.tum.de) proof assistant.

If you have proved additional ones or know of any, please
[send me email](mailto:gerwin.klein@data61.csiro.au) so I can add them here.

If the theorem is not part of the Isabelle distribution, the entry will usually contain a
link to the repository that does. The list does not automatically track the most recent
version of each theorem. If you find one that that is out of date and would like me to
update it, let me know.


1. Square Root of 2 is Irrational
    ```Isabelle
    theorem sqrt_prime_irrational:
      assumes "prime (p::nat)"
      shows "sqrt p ∉ ℚ"
      
    corollary sqrt_2_not_rat: "sqrt 2 ∉ ℚ"
    ```
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Sqrt.html>
  
2. Fundamental Theorem of Algebra
    ```Isabelle
    lemma fundamental_theorem_of_algebra:
      assumes nc: "¬ constant (poly p)"
      shows "∃z::complex. poly p z = 0"
    ```
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Computational_Algebra/Fundamental_Theorem_Algebra.html>
  
3. Denumerability of the Rational Numbers
    ```Isabelle
    theorem rat_denum: "∃f :: nat ⇒ rat. surj f"
    ```
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Library/Countable.html>
  
4. Pythagorean Theorem
    ```Isabelle
    lemma Pythagoras:
      fixes A B C :: "'a :: real_inner"
      assumes "orthogonal (A - C) (B - C)"
      shows "(dist B C) ^ 2 + (dist C A) ^ 2 = (dist A B) ^ 2"
    ```
    
    <https://www.isa-afp.org/entries/Triangle.html>

5. Prime Number Theorem
    Avigad *et al.* formalised the elementary Erdős–Selberg proof:
    ```Isabelle
    definition pi :: "nat ⇒ real"
      where "pi x = real (card {y::nat. y ≤ x ∧ prime y})"
    
    lemma PrimeNumberTheorem: "(λx. pi x * ln (real x) / real x) ⇢ 1"
    ```
    <http://www.andrew.cmu.edu/user/avigad/isabelle/NumberTheory/PrimeNumberTheorem.html>

    A formalisation by Eberl and Paulson of the shorter analytic proof is available in the AFP:

    ```Isabelle
    definition primes_pi :: "real ⇒ real" where
      "primes_pi x = real (card {p::nat. prime p ∧ p ≤ x})"
    
    corollary prime_number_theorem: "primes_pi ∼[at_top] (λx. x / ln x)"
    ```
    <https://www.isa-afp.org/entries/Prime_Number_Theorem.html>

6. Gödel's Incompleteness Theorem

    ```Isabelle
    theorem Goedel_I:
      assumes "¬ {} ⊢ Fls"
        obtains δ where "{} ⊢ δ IFF Neg (PfP ⌈δ⌉)"
                        "¬ {} ⊢ δ"
                        "¬ {} ⊢ Neg δ"
                        "eval_fm e δ"
                        "ground_fm δ"

    theorem Goedel_II:
      assumes "¬ {} ⊢ Fls"
      shows "¬ {} ⊢ Neg (PfP ⌈Fls⌉)"
    ```
    <https://isa-afp.org/entries/Incompleteness.shtml>

7. Law of Quadratic Reciprocity

    ```Isabelle
    theorem Quadratic_Reciprocity:
      assumes "prime p" "2 < p" "prime q" "2 < q" "p ≠ q"
      shows "Legendre p q * Legendre q p = (-1) ^ ((p - 1) div 2 * ((q - 1) div 2))"
    ```
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Number_Theory/Quadratic_Reciprocity.html>

8. The Impossibility of Trisecting the Angle and Doubling the Cube
    ```Isabelle
    theorem impossibility_of_doubling_the_cube:
      "x^3 = 2 ⟹ (Point x 0) ∉ constructible"
    
    theorem impossibility_of_trisecting_angle_pi_over_3:
      "Point (cos (pi / 9)) 0 ∉ constructible"
    ```
    <https://isa-afp.org/entries/Impossible_Geometry.shtml>

9. The Area of a Circle
    ```Isabelle
    theorem content_ball:
      fixes c :: "'a :: euclidean_space"
      assumes "r ≥ 0"
      shows   "content (ball c r) = pi powr (DIM('a) / 2) / Gamma (DIM('a) / 2 + 1) * r ^ DIM('a)"
    
    corollary content_circle:
      "r ≥ 0 ⟹ content (ball c r :: (real ^ 2) set) = r ^ 2 * pi"
    ```
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Ball_Volume.html>

10. Euler's Generalisation of Fermat's Little Theorem

    ```Isabelle
    lemma euler_theorem:
      fixes a m :: nat
      assumes "coprime a m"
      shows "[a ^ totient m = 1] (mod m)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Number_Theory/Residues.html>

11. The Infinitude of Primes

    ```Isabelle
    lemma primes_infinite: "¬finite {p::nat. prime p}"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Computational_Algebra/Primes.html>

12. The Independence of the Parallel Postulate

    <https://isa-afp.org/entries/Tarskis_Geometry.shtml>

13. Polyhedron Formula

    not formalised in Isabelle yet

14. Euler's Summation of 1 + (1/2)^2 + (1/3)^2 + ....

    ```Isabelle
    theorem inverse_squares_sums: "(λn. 1 / (n + 1)²) sums (pi² / 6)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Gamma_Function.html>

    A generalisation of this to all even powers is also available in the AFP:

    ```Isabelle
    corollary nat_even_power_sums_real:
      assumes n: "n > 0"
      shows   "(λk. 1 / real (k+1) ^ (2*n)) sums
                ((-1) ^ (n+1) * bernoulli (2*n) * (2*pi) ^ (2*n) / (2 * fact (2*n)))"
    ```
  
    <https://www.isa-afp.org/browser_info/current/AFP/Bernoulli/Bernoulli_Zeta.html>


15. Fundamental Theorem of Integral Calculus

    ```Isabelle
    theorem fundamental_theorem_of_calculus:
      fixes f :: "real ⇒ 'a :: banach"
      assumes "a ≤ b" 
        and   "⋀x. x ∈ {a..b} ⟹ (f has_vector_derivative f' x) (at x within {a..b})"
      shows   "(f' has_integral (f b - f a)) {a..b}"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Henstock_Kurzweil_Integration.html>
  

16. Insolvability of General Higher Degree Equations

    not formalised in Isabelle yet

17. DeMoivre's Theorem

    ```Isabelle
    lemma DeMoivre: "(cis a) ^ n = cis (real n * a)"

    lemma DeMoivre2: "(rcis r a) ^ n = rcis (r ^ n) (real n * a)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Complex.html>

18. Liouville's Theorem and the Construction of Transcendental Numbers

    ```Isabelle
    corollary transcendental_liouville_constant:
      "¬algebraic (standard_liouville (λ_. 1) 10)"
    ```

    <https://isa-afp.org/entries/Liouville_Numbers.shtml>

19. Lagrange's Four-Square Theorem

    ```Isabelle
    theorem four_squares: "∃a b c d::nat. n = a² + b² + c² + d²"
    ```

    <https://www.isa-afp.org/entries/SumSquares.html>

20. All Primes (1 mod 4) Equal the Sum of Two Squares

    ```Isabelle
    theorem two_squares:
      assumes "prime (p :: nat)"
      shows   "(∃a b. p = a² + b²) ⟷ [p ≠ 3] (mod 4)
    ```

    <https://www.isa-afp.org/entries/SumSquares.html>

21. Green's theorem

    ```Isabelle
    lemma GreenThm_typeI_typeII_divisible_region:
      assumes only_vertical_division:
        "only_vertical_division one_chain_typeI two_chain_typeI"
        "boundary_chain one_chain_typeI" and
        only_horizontal_division:
        "only_horizontal_division one_chain_typeII two_chain_typeII"
        "boundary_chain one_chain_typeII" and
        typeI_and_typII_one_chains_have_common_subdiv:
        "common_boundary_sudivision_exists one_chain_typeI one_chain_typeII"
      shows "integral s (λx. partial_vector_derivative (λx. (F x) ∙ j) i x - partial_vector_derivative (λx. (F x) ∙ i) j x) =
               one_chain_line_integral F {i, j} one_chain_typeI"
            "integral s (λx. partial_vector_derivative (λx. (F x) ∙ j) i x - partial_vector_derivative (λx. (F x) ∙ i) j x) =
               one_chain_line_integral F {i, j} one_chain_typeII"    
    ```

    <https://www.isa-afp.org/entries/Green.html>

22. The Non-Denumerability of the Continuum

    ```Isabelle
    theorem real_non_denum: "∄f :: nat ⇒ real. surj f"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Continuum_Not_Denumerable.html>

23. Formula for Pythagorean Triples

    ```Isabelle
    theorem nat_euclid_pyth_triples:
      fixes a b c :: nat
      assumes "coprime a b" "odd a" "a² + b² = c²"
      shows   "∃p q. a = p² - q² ∧ b = 2 * p * q ∧ c = p² + q² ∧ coprime p q"
    ```

    <https://www.isa-afp.org/entries/Fermat3_4.html>

24. The Undecidability of the Continuum Hypothesis

    not formalised in Isabelle yet

25. Schröder–Bernstein Theorem

    ```Isabelle
    theorem Schroeder_Bernstein:
      fixes f :: "'a ⇒ 'b" and g :: "'b ⇒ 'a"
        and A :: "'a set" and B :: "'b set"
      assumes "inj_on f A" and "f ` A ⊆ B"
        and   "inj_on g B" and "g ` B ⊆ A"
      shows   "∃h. bij_betw h A B"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Inductive.html>

26. Leibnitz's Series for Pi

    ```Isabelle
     theorem pi_series:
       "pi / 4 = (∑k. (-1)^k * 1 / real (k*2+1))"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Transcendental.html>

27. Sum of the Angles of a Triangle

    ```Isabelle
    lemma angle_sum_triangle:
      assumes "a ≠ b ∨ b ≠ c ∨ a ≠ c"
      shows   "angle c a b + angle a b c + angle b c a = pi"
    ```

    <https://isa-afp.org/entries/Triangle.shtml>
    
28. Pascal's Hexagon Theorem

    not formalised in Isabelle yet

29. Feuerbach's Theorem

    not formalised in Isabelle yet

30. The Ballot Problem

    ```Isabelle
    lemma "valid_countings a b = (if a ≤ b then (if b = 0 then 1 else 0) else (a - b) / (a + b) * all_countings a b)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Ballot.html>

31. Ramsey's Theorem

    ```Isabelle
    lemma ramsey:
      fixes r s :: nat and Y :: "'a set" and f :: "'a set ⇒ nat"
      assumes "infinite Y"
      assumes "∀X. X ⊆ Y ∧ finite X ∧ card X = r ⟶ f X < s"
      obtains Y' t where
        "Y' ⊆ Y" and "infinite Y'" and "t < s" and
        "∀X. X ⊆ Y' ∧ finite X ∧ card X = r ⟶ f X = t"
      using ramsey assms by metis
    ```

    <https://isa-afp.org/entries/Ramsey-Infinite.shtml>
    
32. The Four Color Problem

    not formalised in Isabelle yet

33. Fermat's Last Theorem

    not formalised in Isabelle yet

34. Divergence of the Harmonic Series

    ```Isabelle
    theorem not_summable_harmonic:
      shows "¬summable (λn. 1 / real (n + 1))"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Summation_Tests.html>

35. Taylor's Theorem

    ```Isabelle
    theorem taylor:
      fixes a :: real and n :: nat and f :: "real ⇒ real"
      assumes "n > 0" and "diff 0 = f"
        and   "∀m t. m < n ∧ t ∈ {a..b} ⟶ (diff m has_real_derivative diff (m + 1) t) (at t)"
        and   "c ∈ {a..b}" and "x ∈ {a..b} - {c}"
      shows "∃t. t ∈ open_segment x c ∧
                 f x = (∑m<n. (diff m c / fact m) * (x - c) ^ m) + (diff n t / fact n) * (x - c) ^ n"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/MacLaurin.html>

36. Brouwer Fixed Point Theorem

    ```Isabelle
    lemma brouwer:
      fixes f :: "'a::euclidean_space ⇒ 'a"
      assumes "compact S" and "convex S" and "S ≠ {}"
          and "continuous_on S f"
          and "f ` S ⊆ S"
          obtains x where "x ∈ S" and "f x = x"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Brouwer_Fixpoint.html>

37. The Solution of a Cubic

    ```Isabelle
    lemma cubic:
      assumes a0: "a ≠ 0"
      shows "
      let p = (3 * a * c - b^2) / (9 * a^2) ;
          q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3);
          s = csqrt(q^2 + p^3);
          s1 = (if p = 0 then ccbrt(2 * q) else ccbrt(q + s));
          s2 = -s1 * (1 + ii * csqrt 3) / 2;
          s3 = -s1 * (1 - ii * csqrt 3) / 2
      in if p = 0 then
           a * x^3 + b * x^2 + c * x + d = 0 ⟷
               x = s1 - b / (3 * a) ∨
               x = s2 - b / (3 * a) ∨
               x = s3 - b / (3 * a)
          else
            s1 ≠ 0 ∧
            (a * x^3 + b * x^2 + c * x + d = 0 ⟷
                x = s1 - p / s1 - b / (3 * a) ∨
                x = s2 - p / s2 - b / (3 * a) ∨
                x = s3 - p / s3 - b / (3 * a))"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Cubic_Quartic.html>

38. Arithmetic Mean / Geometric Mean

    ```Isabelle
    theorem CauchysMeanTheorem:
      fixes z :: "real list"
      assumes "pos z"
      shows "gmean z ≤ mean z"
      
    theorem CauchysMeanTheorem_Eq:
      fixes z :: "real list"
      assumes "pos z"
      shows "gmean z = mean z ⟷ het z = 0"
    ```

    <https://isa-afp.org/entries/Cauchy.shtml>

39. Solutions to Pell's Equation

    ```Isabelle
    theorem pell_solutions:
      fixes D :: nat
      assumes "∄k. D = k²"
      obtains "x₀" "y₀" :: nat
      where   "∀(x::int) (y::int).
                 x² - D * y² = 1 ⟷
                (∃n::nat. nat ¦x¦ + sqrt D * nat ¦y¦ = (x₀ + sqrt D * y₀) ^ n)"

    corollary pell_solutions_infinite:
      fixes D :: nat
      assumes "∄k. D = k²"
      shows   "infinite {(x :: int, y :: int). x² - D * y² = 1}"
    ```

    <https://www.isa-afp.org/entries/Pell.html>

40. Minkowski's Fundamental Theorem

    ```Isabelle
    theorem minkowski:
      fixes B :: "(real ^ 'n) set"
      assumes "convex B" and symmetric: "uminus ` B ⊆ B"
      assumes meas_B [measurable]: "B ∈ sets lebesgue"
      assumes measure_B: "emeasure lebesgue B > 2 ^ CARD('n)"
      obtains x where "x ∈ B" and "x ≠ 0" and "⋀i. x $ i ∈ ℤ"
    ```

    <https://www.isa-afp.org/entries/Minkowskis_Theorem.shtml>

41. Puiseux's Theorem

42. Sum of the Reciprocals of the Triangular Numbers

    ```Isabelle
    definition triangle_num :: "nat ⇒ nat" where
      "triangle_num n = (n * (n + 1)) div 2"

    theorem inverse_triangle_num_sums:
      "(λn. 1 / triangle_num (Suc n)) sums 2"
    ```

    <https://isabelle.in.tum.de/library/HOL/HOL-ex/Triangular_Numbers.html>

43. The Isoperimetric Theorem

    not formalised in Isabelle yet

44. The Binomial Theorem

    ```Isabelle
    theorem binomial_ring:
      fixes a b :: "'a :: comm_ring_1"
      shows "(a + b) ^ n = (∑k=0..n. of_nat (n choose k) * a ^ k * b ^ (n - k))"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Binomial.html>

45. The Partition Theorem

    ```Isabelle
    theorem Euler_partition_theorem:
      "card {p. p partitions n ∧ (∀i. p i ≤ 1)} = card {p. p partitions n ∧ (∀i. p i ≠ 0 ⟶ odd i)}"
    ```

    <https://isa-afp.org/entries/Euler_Partition.shtml>

46. The Solution of the General Quartic Equation

    ```Isabelle
    lemma quartic:
      "(y::real)^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0 ∧
       R^2 = a^2 / 4 - b + y ∧
       s^2 = y^2 - 4 * d ∧
       (D^2 = (if R = 0 then 3 * a^2 / 4 - 2 * b + 2 * s
                        else 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R))) ∧
       (E^2 = (if R = 0 then 3 * a^2 / 4 - 2 * b - 2 * s
                       else 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R)))
       ⟹ x^4 + a * x^3 + b * x^2 + c * x + d = 0 ⟷
          x = -a / 4 + R / 2 + D / 2 ∨
          x = -a / 4 + R / 2 - D / 2 ∨
          x = -a / 4 - R / 2 + E / 2 ∨
          x = -a / 4 - R / 2 - E / 2"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Cubic_Quartic.html>

47. The Central Limit Theorem

    ```Isabelle
    theorem (in prob_space) central_limit_theorem:
      fixes
        X :: "nat ⇒ 'a ⇒ real" and
        μ :: "real measure" and
        σ :: real and
        S :: "nat ⇒ 'a ⇒ real"
      assumes
        X_indep: "indep_vars (λi. borel) X UNIV" and
        X_mean_0: "⋀n. expectation (X n) = 0" and
        σ_pos: "σ > 0" and
        X_square_integrable: "⋀n. integrable M (λx. (X n x)⇧2)" and
        X_variance: "⋀n. variance (X n) = σ⇧2" and
        X_distrib: "⋀n. distr M borel (X n) = μ"
      defines
        "S n ≡ λx. ∑i<n. X i x"
      shows
        "weak_conv_m (λn. distr M borel (λx. S n x / sqrt (n * σ⇧2)))
            (density lborel std_normal_density)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Probability/Central_Limit_Theorem.html>

48. Dirichlet's Theorem

    ```Isabelle
    theorem Dirichlet:
      assumes "n > 1" and "coprime h n"
      shows   "infinite {p. prime p ∧ [p = h] (mod n)}"
    ```

    <https://isa-afp.org/entries/Dirichlet_L.html>

49. Cayley-Hamilton Theorem

    ```Isabelle
    theorem Cayley_Hamilton:
      fixes A :: "'a :: comm_ring_1 ^ ('n :: finite) ^ 'n"
      shows "evalmat (charpoly A) A = 0"
    ```

    <https://isa-afp.org/entries/Cayley_Hamilton.shtml>

50. The Number of Platonic Solids

    not formalised in Isabelle yet

51. Wilson's Theorem

    ```Isabelle
    lemma wilson_theorem:
      assumes "prime p"
      shows   "[fact (p - 1) = -1] (mod p)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Number_Theory/Residues.html>

52. The Number of Subsets of a Set

    ```Isabelle
    lemma card_Pow:
      "finite A ⟹ card (Pow A) = 2 ^ card A"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Power.html>

53. Pi is Transcendental

    ```Isabelle
    theorem transcendental_pi: "¬algebraic pi"
    ```

    <https://www.isa-afp.org/entries/Pi_Transcendental.html>

54. The Koenigsberg Bridges Problem

    ```Isabelle
    lemma eulerian_split:
      assumes "nodes G1 ∩ nodes G2 = {}" "edges G1 ∩ edges G2={}"
        "valid_unMultigraph G1" "valid_unMultigraph G2"
        "valid_unMultigraph.is_Eulerian_trail  G1 v1 ps1 v1'"
        "valid_unMultigraph.is_Eulerian_trail  G2 v2 ps2 v2'"
      shows "valid_unMultigraph.is_Eulerian_trail ⦇nodes=nodes G1 ∪ nodes G2,
              edges=edges G1 ∪ edges G2 ∪ {(v1',w,v2),(v2,w,v1')}⦈ v1 (ps1@(v1',w,v2)#ps2) v2'"
    ```

    <https://isa-afp.org/entries/Koenigsberg_Friendship.shtml>

55. Product of Segments of Chords

    ```Isabelle
    theorem product_of_chord_segments:
      fixes S1 T1 S2 T2 X C :: "'a :: euclidean_space"
      assumes "between (S1, T1) X" "between (S2, T2) X"
      assumes "dist C S1 = r" "dist C T1 = r"
      assumes "dist C S2 = r" "dist C T2 = r"
      shows "dist S1 X * dist X T1 = dist S2 X * dist X T2"
    ```

    <https://www.isa-afp.org/entries/Chord_Segments.shtml>


56. The Hermite-Lindemann Transcendence Theorem

    not formalised in Isabelle yet

57. Heron's formula

    ```Isabelle
    theorem heron:
      fixes A B C :: "real ^ 2"
      defines "a ≡ dist B C" and "b ≡ dist A C" and "c ≡ dist A B"
      defines "s ≡ (a + b + c) / 2"
      shows   "content (convex hull {A, B, C}) = sqrt (s * (s - a) * (s - b) * (s - c))"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Simplex_Content.html>

58. Formula for the Number of Combinations

    ```Isabelle
    theorem n_subsets:
      "finite A ⟹ card {B. B ⊆ A ∧ card B = k} = (card A choose k)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Binomial.html>

59. The Laws of Large Numbers

    ```Isabelle
    theorem (in prob_space) strong_law_of_large_numbers_iid:
      fixes X :: "nat ⇒ 'a ⇒ real"
      assumes indep: "indep_vars (λ_. borel) X UNIV"
      assumes distr: "⋀i. distr M borel (X i) = distr M borel (X 0)"
      assumes L1:    "integrable M (X 0)"
      shows   "AE x in M. (λn. (∑i<n. X i x) / n) ⇢ expectation (X 0)"
    ```
    
    <https://www.isa-afp.org/entries/Laws_of_Large_Numbers.html>
    
60. Bezout's Theorem

    ```Isabelle
      lemma (in euclidean_ring_gcd) bezout_coefficients:
        "bezout_coefficients a b = (x, y) ⟹ x * a + y * b = gcd a b"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Computational_Algebra/Euclidean_Algorithm.html>

61. Theorem of Ceva

    not formalised in Isabelle yet

62. Fair Games Theorem

    not formalised in Isabelle yet

63. Cantor's Theorem

    ```Isabelle
    lemma Cantors_paradox: ∄f. f ` A = Pow A
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Fun.html>

64. L'Hôpital's Rule

    ```Isabelle
    lemma lhopital:
      fixes f g f' g' :: "real ⇒ real"
      assumes "f ─x→ 0" and "g ─x→ 0"
      assumes "∀⇩F u in at x. g u ≠ 0" 
      assumes "∀⇩F u in at x. g' u ≠ 0"
      assumes "∀⇩F u in at x. (f has_real_derivative f' u) (at u)"
      assumes "∀⇩F u in at x. (g has_real_derivative g' u) (at u)"
      assumes "filterlim (λx. f' x / g' x) F (at x)"
      shows   "filterlim (λx. f x / g x) F (at x)"
      ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Deriv.html>

65. Isosceles Triangle Theorem

    ```Isabelle
    lemma isosceles_triangle:
      assumes "dist a c = dist b c"
      shows   "angle b a c = angle a b c"
    ```

    <https://isa-afp.org/entries/Triangle.shtml>

66. Sum of a Geometric Series

    ```Isabelle
    lemma geometric_sums:
      "norm c < 1 ⟹ (λn. c^n) sums (1 / (1 - c))"

    lemma suminf_geometric:
      "norm c < 1 ⟹ (∑n. c ^ n) = 1 / (1 - c)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Series.html>

67. e is Transcendental

    ```Isabelle
    corollary e_transcendental_real: "¬ algebraic (exp 1 :: real)"
    ```

    <https://www.isa-afp.org/entries/E_Transcendental.shtml>

68. Sum of an Arithmetic Series

    ```Isabelle
    lemma double_arith_series:
      fixes a d :: "'a :: comm_semiring_1"
      shows "2 * (∑i=0..n. a + of_nat i * d) = (of_nat n + 1) * (2 * a + of_nat n * d)"
    ```

69. Greatest Common Divisor Algorithm

    The greatest common divisor is defined in the `semiring_gcd` typeclass. Instances are provided for all the basic types, such as naturals, integers, and polynomials.
    The most important properties are:

    ```Isabelle
    lemma gcd_dvd1:     "gcd a b dvd a"
      and gcd_dvd2:     "gcd a b dvd b"
      and gcd_greatest: "c dvd a ⟹ c dvd b ⟹ c dvd gcd a b"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/GCD.html>

70. Perfect Number Theorem

    ```Isabelle
    theorem perfect_number_theorem:
      assumes even: "even m" and perfect: "perfect m"
      shows "∃n. m = 2^n*(2^(n+1) - 1) ∧ prime ((2::nat)^(n+1) - 1)"
    ```

    <https://isa-afp.org/entries/Perfect-Number-Thm.shtml>

71. Order of a Subgroup

    ```Isabelle
    proposition (in group) lagrange_finite:
      assumes "finite (carrier G)" and "subgroup H G"
      shows "card (rcosets H) * card H = order G"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Algebra/Coset.html>

72. Sylow's Theorem

    ```Isabelle
    theorem sylow_thm:
      assumes "prime p" and "group G" and "order G = p ^ a * m" and "finite (carrier G)"
      obtains H where "subgroup H G" and "card H = p ^ a"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Algebra/Sylow.html>

73. Ascending or Descending Sequences

    ```Isabelle
    lemma Erdoes_Szekeres:
      fixes f :: "_ ⇒ 'a::linorder"
      shows "(∃S. S ⊆ {0..m * n} ∧ card S = m + 1 ∧ mono_on f (op ≤) S) ∨
             (∃S. S ⊆ {0..m * n} ∧ card S = n + 1 ∧ mono_on f (op ≥) S)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Erdoes_Szekeres.html>

74. The Principle of Mathematical Induction

    ```Isabelle
    theorem nat_induct:
      fixes n :: nat
      assumes "P 0" and "⋀n. P n ⟹ P (n + 1)"
      shows   "P n"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Nat.html>

75. The Mean Value Theorem


    ```Isabelle
    theorem MVT:
      fixes a b :: real and f :: "real ⇒ real"
      assumes "a < b"
          and "∀x∈{a..b}. isCont f x"
          and "∀x∈{a<..<b}. f differentiable (at x)"
      shows "∃l z. z ∈ {a<..<b} ∧ (f has_real_derivative l) (at z) ∧
                 f b - f a = (b - a) * l"

    lemma MVT2:
      fixes a b :: real and f f' :: "real ⇒ real"
      assumes "a < b"
          and "∀x∈{a..b}. (f has_real_derivative f' x) (at x)"
      shows "∃z. z ∈ {a<..<b} ∧ f b - f a = (b - a) * f' z"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Deriv.html>

76. Fourier Series

    ```Isabelle
    corollary Fourier_Fejer_Cesaro_summable_simple:
      assumes f: "continuous_on UNIV f"
          and periodic: "⋀x. f (x + 2*pi) = f x"
      shows "(λn. (∑m<n. ∑k≤2*m. Fourier_coefficient f k * trigonometric_set k x) / n) ⇢ f x"
    ```
    
    <https://www.isa-afp.org/entries/Fourier.html>

77. Sum of k-th powers

    ```Isabelle
    lemma sum_of_powers:
      fixes m n :: nat
      shows "(∑k=0..n. k ^ m) = (bernpoly (m + 1) (n + 1) - bernpoly (m + 1) 0) / (m + 1)"
    ```

    <https://www.isa-afp.org/entries/Bernoulli.html>

78. The Cauchy-Schwarz Inequality

    ```Isabelle
    theorem CauchySchwarzReal:
      fixes x::vector
      assumes "vlen x = vlen y"
      shows "¦x ⋅ y¦ ≤ ∥x∥ * ∥y∥"
    ```
    <https://isa-afp.org/entries/Cauchy.shtml>
  
    An alternative version is available in the standard library:

    ```Isabelle
    lemma Cauchy_Schwarz_ineq2:
      "¦x ∙ y¦ ≤ norm x * norm y"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Inner_Product.html>
 

79. The Intermediate Value Theorem

    ```Isabelle
    lemma IVT':
      fixes f :: "real ⇒ real"
      assumes "a ≤ b" and "y ∈ {f a..f b}" and  "continuous_on {a..b} f"
      obtains x where "x ∈ {a..b}" and "f x = y"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Topological_Spaces.html>

80. Fundamental Theorem of Arithmetic

    The function `prime_factorization` is defined for any factorial semiring. It returns the factorization as a multiset that fulfils the following properties:

    ```Isabelle
    lemma in_prime_factors_iff:
      "p ∈ set_mset (prime_factors x) ⟷ x ≠ 0 ∧ p dvd x ∧ prime p"
    
    lemma prod_mset_prime_factorization:
      assumes "x ≠ 0"
      shows   "prod_mset (prime_factorization x) = normalize x"
    
    lemma prime_factorization_unique:
      assumes "x ≠ 0" "y ≠ 0"
      shows   "prime_factorization x = prime_factorization y ⟷ normalize x = normalize y"
    ```

    The `normalize` function is required because associated elements (like -3 and 3) have the same factorization; for natural numbers, it is the identity.

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Computational_Algebra/Factorial_Ring.html>


81. Divergence of the Prime Reciprocal Series

    ```Isabelle
    corollary prime_harmonic_series_diverges:
      "¬convergent (λn. ∑p←primes_upto n. 1 / p)"
    ```

    <https://isa-afp.org/entries/Prime_Harmonic_Series.shtml>

    The more precise asymptotic estimate given by Mertens' Second Theorem is also available:

    ```Isabelle
    theorem mertens_second_theorem:
      "(λx. (∑p | real p ≤ x ∧ prime p. 1 / p) - ln (ln x) - meissel_mertens) ∈ O(λx. 1 / ln x)"
    ```

    <https://www.isa-afp.org/entries/Prime_Number_Theorem.html>

82. Dissection of Cubes (J.E. Littlewood's "elegant" proof)

    not formalised in Isabelle yet

83. The Friendship Theorem

    ```Isabelle
    theorem (in valid_unSimpGraph) friendship_thm:
      assumes "⋀v u. v∈V ⟹ u∈V ⟹ v≠u ⟹ ∃! n. adjacent v n ∧ adjacent u n" and "finite V"
      shows "∃v. ∀n∈V. n≠v ⟶ adjacent v n"
    ```

    <https://isa-afp.org/entries/Koenigsberg_Friendship.shtml>

84. Morley's Theorem

    not formalised in Isabelle yet

85. Divisibility by Three Rule

    ```Isabelle
    theorem three_divides_nat: "3 dvd n ⟷ 3 dvd sumdig n"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/ThreeDivides.html>

86. Lebesgue Measure and Integration

    <https://isa-afp.org/entries/Integration.shtml>

    A more recent and more extensive library of the Lebesgue Measure and Lebesgue integration (and also the Bochner integral and the Henstock–Kurzweil integral and the connections between all of these) is also in the standard distribution:

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Lebesgue_Measure.html>

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Nonnegative_Lebesgue_Integration.html>
  
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Bochner_Integration.html>
  
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Henstock_Kurzweil_Integration.thy.html>
  
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Equivalence_Lebesgue_Henstock_Integration.thy.html>

87. Desargues's Theorem

    ```Isabelle
    theorem desargues_3D:
      assumes "desargues_config_3D A B C A' B' C' P α β γ"
      shows "rk {α, β, γ} ≤ 2"
    ```
    
    <https://www.isa-afp.org/entries/Projective_Geometry.html>

88. Derangements Formula

    ```Isabelle
    theorem derangements_formula:
      assumes "n ≠ 0" and "finite S" and "card S = n"
      shows "card (derangements S) = round (fact n / exp 1)"
    ```

    <https://isa-afp.org/entries/Derangements.shtml>

89. The Factor and Remainder Theorems

    ```Isabelle
    lemma long_div_theorem:
      assumes "g ∈ carrier P" and "f ∈ carrier P" and "g ≠ 𝟬⇘P⇙"
      shows "∃q r (k::nat). (q ∈ carrier P) ∧ (r ∈ carrier P) ∧
            (lcoeff g)(^)⇘R⇙k ⊙⇘P⇙ f = g ⊗⇘P⇙ q ⊕⇘P⇙ r ∧
            (r = 𝟬⇘P⇙ | deg R r < deg R g)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Algebra/UnivPoly.html>

    Independently, `HOL-Computational_Algebra` provides notions of division and remainder in Euclidean rings (such as naturals, integers, polynomials):

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Computational_Algebra/Euclidean_Algorithm.html>

90. Stirling's Formula

    The following gives the full asymptotic expansion of the complex log-Gamma function, and, derived from that, the first term of the asymptotic expansion of the complex Gamma function:

    ```Isabelle
    theorem ln_Gamma_complex_asymptotics_explicit:
      fixes m :: nat and α :: real
      assumes "m > 0" and "α ∈ {0<..<pi}"
      obtains C :: real and R :: "complex ⇒ complex"
      where "∀s::complex. s ∉ ℝ⇩≤⇩0 ⟶
                   ln_Gamma s = (s - 1/2) * ln s - s + ln (2 * pi) / 2 +
                                (∑k=1..<m. bernoulli (k+1) / (k * (k+1) * s ^ k)) - R s"
        and "∀s. s ≠ 0 ∧ ¦arg s¦ ≤ α ⟶ norm (R s) ≤ C / norm s ^ m"
        
    lemma Gamma_complex_asymp_equiv:
      fixes α :: real
      assumes α: "α ∈ {0<..<pi}"
      defines "F ≡ inf at_infinity (principal (complex_cone' α))"
      shows   "Gamma ∼[F] (λs. sqrt (2 * pi) * (s / exp 1) powr s / s powr (1 / 2))"
    ```

    There are also these slightly simpler versions for the real Gamma function and the factorial:
    
    ```Isabelle
    theorem Gamma_asymp_equiv:
      "Gamma ∼ (λx. sqrt (2*pi/x) * (x / exp 1) powr x :: real)"

    theorem fact_asymp_equiv:
      "fact ∼ (λn. sqrt (2*pi*n) * (n / exp 1) ^ n :: real)"
    ```
  
    <https://www.isa-afp.org/entries/Stirling_Formula.shtml>
  
    <https://www.isa-afp.org/entries/Gamma_Asymptotics.shtml>


91. The Triangle Inequality

    ```Isabelle
    class ordered_ab_group_add_abs = ordered_ab_group_add + abs +
      assumes abs_ge_zero: "¦a¦ ≥ 0"
        and abs_ge_self: "a ≤ ¦a¦"
        and abs_leI: "a ≤ b ⟹ - a ≤ b ⟹ ¦a¦ ≤ b"
        and abs_minus_cancel: "¦-a¦ = ¦a¦"
        and abs_triangle_ineq: "¦a + b¦ ≤ ¦a¦ + ¦b¦"
    ```

    The triangle inequality is a type class property in Isabelle. Real numbers, integers, etc are instances of this type class:

    ```Isabelle
    lemma abs_triangle_ineq_real: "¦(a::real) + b¦ ≤ ¦a¦ + ¦b¦"
    lemma abs_triangle_ineq_int: "¦(a::int) + b¦ ≤ ¦a¦ + ¦b¦"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Groups.html>

92. Pick's Theorem

    not formalised in Isabelle yet

93. The Birthday Problem

    ```Isabelle
    lemma birthday_paradox:
      assumes "card S = 23" "card T = 365"
      shows "2 * card {f ∈ S→⇩E S T. ¬ inj_on f S} ≥ card (S →⇩E T)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Birthday_Paradox.html>

94. The Law of Cosines

    ```Isabelle
    lemma cosine_law_triangle:
      "dist b c ^ 2 = dist a b ^ 2 + dist a c ^ 2 - 2 * dist a b * dist a c * cos (angle b a c)"
    ```

    <https://isa-afp.org/entries/Triangle.shtml>

95. Ptolemy's Theorem

    ```Isabelle
    theorem ptolemy:
      fixes A B C D center :: "real ^ 2"
      assumes "dist center A = radius" and "dist center B = radius"
      assumes "dist center C = radius" and "dist center D = radius"
      assumes ordering_of_points:
        "radiant_of (A - center) ≤ radiant_of (B - center)"
        "radiant_of (B - center) ≤ radiant_of (C - center)"
        "radiant_of (C - center) ≤ radiant_of (D - center)"
      shows "dist A C * dist B D = dist A B * dist C D + dist A D * dist B C"
    ```

    <https://www.isa-afp.org/entries/Ptolemys_Theorem.shtml>

96. Principle of Inclusion/Exclusion

    ```Isabelle
    lemma card_UNION:
      assumes "finite A" and "∀k ∈ A. finite k"
      shows "card (⋃A) = nat (∑I | I ⊆ A ∧ I ≠ {}. (- 1) ^ (card I + 1) * int (card (⋂I)))"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Binomial.html>

97. Cramer's Rule

    ```Isabelle
    lemma cramer:
      fixes A ::"real^'n^'n"
      assumes d0: "det A ≠ 0"
      shows "A *v x = b ⟷ x = (χ k. det(χ i j. if j=k then b$i else A$i$j) / det A)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Determinants.html>

98. Bertrand's Postulate

    ```Isabelle
    theorem bertrand: "n > 1 ⟹ ∃p∈{n<..<2*n}. prime p"
    ```

    <https://www.isa-afp.org/entries/Bertrands_Postulate.shtml>

99. Buffon Needle Problem

    ```Isabelle
    definition needle :: "real ⇒ real ⇒ real ⇒ real set" where
      "needle l x φ = closed_segment (x - l / 2 * sin φ) (x + l / 2 * sin φ)"
    
    locale Buffon =
      fixes d l :: real
      assumes d: "d > 0" and l: "l > 0"
    begin
    
    definition Buffon :: "(real × real) measure" where
      "Buffon = uniform_measure lborel ({-d/2..d/2} × {-pi..pi})"
    
    theorem prob_short:
      "𝒫((x,φ) in Buffon. needle l x φ ∩ {-d/2, d/2} ≠ {}) = 2 * l / (d * pi)"
    
    theorem prob_long:
      "𝒫((x,φ) in Buffon. needle l x φ ∩ {-d/2, d/2} ≠ {}) =
         2 / pi * ((l / d) - sqrt ((l / d)² - 1) + arccos (d / l))"
         
    end
    ```
    <https://www.isa-afp.org/entries/Buffons_Needle.shtml>

1. Descartes Rule of Signs
    ```Isabelle
    theorem descartes_sign_rule:
      fixes p :: "real poly"
      assumes "p ≠ 0"
      shows "∃d. even d ∧ coeff_sign_changes p = count_pos_roots p + d"
    ```
    <https://isa-afp.org/entries/Descartes_Sign_Rule.shtml>
    
    
1. Atiyah-Singer Index Theorem

    not formalised in Isabelle yet
    
1. Baker's Theorem on Linear Forms in Logarithms

    not formalised in Isabelle yet
   
1. Black-Scholes Formula

    not formalised in Isabelle yet
    
1. Borsuk-Ulam Theorem

    not formalised in Isabelle yet
    
1. Cauchy's Integral Theorem

    ```Isabelle
    proposition Cauchy_theorem_homotopic_paths:
      assumes hom: "homotopic_paths s g h"
          and "open s" and f: "f holomorphic_on s"
          and vpg: "valid_path g" and vph: "valid_path h"
      shows "contour_integral g f = contour_integral h f"

    proposition Cauchy_theorem_homotopic_loops:
      assumes hom: "homotopic_loops s g h"
          and "open s" and f: "f holomorphic_on s"
          and vpg: "valid_path g" and vph: "valid_path h"
      shows "contour_integral g f = contour_integral h f"
    ```
  
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Complex_Analysis/Cauchy_Integral_Theorem.html>
  
  
1. Cauchy's Residue Theorem

    ```Isabelle
    theorem Residue_theorem:
      fixes s pts :: "complex set" and f::"complex ⇒ complex"
        and g :: "real ⇒ complex"
      assumes "open s" "connected s" "finite pts" and
              "f holomorphic_on s-pts" and
              "valid_path g" and
              "pathfinish g = pathstart g" and
              "path_image g ⊆ s-pts" and
              "∀z. (z ∉ s) ⟶ winding_number g z = 0"
      shows "contour_integral g f = 2 * pi * 𝗂 * (∑p∈pts. winding_number g p * residue f p)"
    ```
  
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Complex_Analysis/Residue_Theorem.html>
  
1. Chen's theorem

    not formalised in Isabelle yet
    
1. Every vector space is free

    ```isabelle
    lemma (in vector_space) basis_exists:
      obtains B where "B ⊆ V" "independent B" "V ⊆ span B" "card B = dim V"
    ```
    
    <https://isabelle.in.tum.de/dist/library/HOL/HOL/Vector_Spaces.html>
    
1. Classification of Finite Simple Groups

    not formalised in Isabelle yet
    
1. Classification of semisimple Lie groups (Killing, Cartan, Dynkin)

    not formalised in Isabelle yet
    
1. Sophie Germain's theorem

    not formalised in Isabelle yet
 
1. Gödel's Completeness Theorem

    <https://www.isa-afp.org/entries/Completeness.html>
 
1. Gödel's Second Incompleteness Theorem

    ```Isabelle
    theorem Goedel_II: "¬ ({} ⊢ Neg (PfP «Fls»))"
    ```
  
    <https://www.isa-afp.org/entries/Incompleteness.html>

1. Green-Tao Theorem

    not formalised in Isabelle yet
    
1. Feit-Thompson Theorem

    not formalised in Isabelle yet
    
1. Fundamental Theorem of Galois Theory

    not formalised in Isabelle yet
  
1. Heine–Borel Theorem

    Heine–Borel is actually the definition of compactness in Isabelle/HOL in any topological space:

    ```Isabelle
    definition (in topological_space) compact :: "'a set ⇒ bool" where
        "compact S ⟷ (∀C. (∀c∈C. open c) ∧ S ⊆ ⋃C ⟶ (∃D⊆C. finite D ∧ S ⊆ ⋃D))"
    ```
  
    For types of the `heine_borel` type class, this is proven to be equivalent to the set beind bounded and closed:
    ```Isabelle
    lemma compact_eq_bounded_closed:
      fixes s :: "'a :: heine_borel set"
      shows "compact s ⟷ bounded s ∧ closed s"
    ```
  
    It is shown that all Euclidean spaces are Heine–Borel, i.e. that `euclidean_space` is a subclass of `heine_borel`.

    <https://isabelle.in.tum.de/dist/library/HOL/Topological_Spaces.html>  
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Elementary_Metric_Spaces.html>
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Topology_Euclidean_Space.html>
  
  
1. Hessenberg's Theorem = "Pappus → Desargues"

    ```Isabelle
    theorem hessenberg_thereom:
      assumes "is_pappus"
      shows "desargues_prop"
    ```
    
    <https://www.isa-afp.org/entries/Projective_Geometry.html>
    
1. Hilbert Basis Theorem

    not formalised in Isabelle yet
  
1. Hilbert Nullstellensatz

    ```Isabelle
    theorem strong_Nullstellensatz:
      assumes "finite X" and "F ⊆ P[X]"
      shows "ℐ (𝒱 F) = √ideal (F::((_::{countable,linorder} ⇒⇩0 nat) ⇒⇩0 _::alg_closed_field) set)"
    ```

    <https://www.isa-afp.org/entries/Nullstellensatz.html>


1. Hilbert-Waring theorem

    not formalised in Isabelle yet
    
1. Invariance of Dimension

    ```Isabelle
    corollary invariance_of_dimension:
      fixes f :: "'a::euclidean_space ⇒ 'b::euclidean_space"
      assumes contf: "continuous_on S f" and "open S"
          and injf: "inj_on f S" and "S ≠ {}"
        shows "DIM('a) ≤ DIM('b)"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Further_Topology.html>


1. IP=PSPACE

    not formalised in Isabelle yet

1. Jordan Curve Theorem

    ```Isabelle
    corollary Jordan_inside_outside:
      fixes c :: "real ⇒ complex"
      assumes "simple_path c" "pathfinish c = pathstart c"
        shows "inside (path_image c) ≠ {} ∧
               open (inside (path_image c)) ∧
               connected (inside (path_image c)) ∧
               outside (path_image c) ≠ {} ∧
               open (outside (path_image c)) ∧
               connected (outside (path_image c)) ∧
               bounded (inside (path_image c)) ∧
               ¬ bounded (outside (path_image c)) ∧
               inside (path_image c) ∩ outside(path_image c) = {} ∧
               inside (path_image c) ∪ outside(path_image c) = - path_image c ∧
               frontier (inside (path_image c)) = path_image c ∧
               frontier (outside (path_image c)) = path_image c"
    ```

    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Jordan_Curve.html>

1. Kepler Conjecture

    not formalised in Isabelle yet

1. Lie's work relating Algebras and Groups

    not formalised in Isabelle yet
    
1. Nash's Theorem

    not formalised in Isabelle yet
    
1. Perelman-Hamilton-Thurston theorem classifying compact 3-manifolds

    not formalised in Isabelle yet
    
1. Poincaré Conjecture

    not formalised in Isabelle yet

1. Riemann Mapping Theorem

    ```Isabelle
    theorem Riemann_mapping_theorem:
      "open S ∧ simply_connected S ⟷
       S = {} ∨ S = UNIV ∨
       (∃f g. f holomorphic_on S ∧ g holomorphic_on ball 0 1 ∧
             (∀z ∈ S. f z ∈ ball 0 1 ∧ g(f z) = z) ∧
             (∀z ∈ ball 0 1. g z ∈ S ∧ f(g z) = z))"
    ```
  
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Complex_Analysis/Riemann_Mapping.html>
  
  
1. Sorting takes Θ(N log N) steps

    ```Isabelle
    datatype 'a sorter = Return "'a list" | Query 'a 'a "bool ⇒ 'a sorter"
    
    primrec count_queries :: "('a × 'a) set ⇒ 'a sorter ⇒ nat" where
      "count_queries _ (Return _)    = 0"
    | "count_queries R (Query a b f) = 1 + count_queries R (f ((a, b) ∈ R))"

    definition count_wc_queries :: "('a × 'a) set set ⇒ 'a sorter ⇒ nat" where
      "count_wc_queries Rs sorter = (if Rs = {} then 0 else Max ((λR. count_queries R sorter) ` Rs))"
      
    primrec eval_sorter :: "('a × 'a) set ⇒ 'a sorter ⇒ 'a list" where
      "eval_sorter _ (Return ys)   = ys"
    | "eval_sorter R (Query a b f) = eval_sorter R (f ((a,b) ∈ R))"
    
    definition is_sorting :: "('a × 'a) set ⇒ 'a list ⇒ 'a list ⇒ bool" where
      "is_sorting R xs ys ⟷ (mset xs = mset ys) ∧ sorted_wrt R ys"
  
    corollary count_queries_bigomega:
      fixes sorter :: "nat ⇒ nat sorter"
      assumes sorter: "⋀n R. linorder_on {..<n} R ⟹ 
                             is_sorting R [0..<n] (eval_sorter R (sorter n))"
      defines "Rs ≡ λn. {R. linorder_on {..<n} R}"
      shows   "(λn. count_wc_queries (Rs n) (sorter n)) ∈ Ω(λn. n * ln n)"
    ```
  
    <https://www.isa-afp.org/entries/Comparison_Sort_Lower_Bound.html>
  
  
1. Stokes' Theorem

    not formalised in Isabelle yet

  
1. Stone–Weierstraß Theorem
  
    ```Isabelle
    theorem (in function_ring_on) Stone_Weierstrass:
      assumes f: "continuous_on S f"
      shows "∃F∈UNIV → R. uniform_limit S F f sequentially 
      
    proposition Stone_Weierstrass_uniform_limit:
      fixes f :: "'a::euclidean_space ⇒ 'b::euclidean_space"
      assumes S: "compact S"
        and f: "continuous_on S f"
      obtains g where "uniform_limit S g f sequentially" and "⋀n. polynomial_function (g n)"
    ```
  
    <https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Weierstrass_Theorems.html>
  
1. Thales' Theorem
  
    ```Isabelle
    theorem thales:
      fixes A B C :: "'a :: real_inner"
      assumes "dist B (midpoint A C) = dist A C / 2"
      shows   "orthogonal (A - B) (C - B)"
    ```  
  
    <https://www.isa-afp.org/entries/Triangle.html>

1. Yoneda lemma

    <https://www.isa-afp.org/entries/Category.html>
    <https://www.isa-afp.org/entries/Category2.html>
    <https://www.isa-afp.org/entries/Category3.html>

1. ζ(-1) = -1 / 12
  
    ```Isabelle
    theorem zeta_even_nat: 
      "zeta (2 * of_nat n) = 
         of_real ((-1) ^ (n+1) * bernoulli (2*n) * (2*pi)^(2*n) / (2 * fact (2*n)))"
  
    corollary zeta_neg1: "zeta (-1) = - 1 / 12"
    ```
  
    <https://www.isa-afp.org/entries/Zeta_Function.html>
  
  

