-- Prove2me | solution 1 for OAI.TotientAsymptotic.terminal_prefix_mass_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:40:06.553668+00:00
-- url     : https://prove2.me/submissions/7e6d7eb1-7ec1-4b43-a32e-eccfde0dfd7e

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_smooth_terminal_mass_bound

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal totient majorants, including repeated primes in the cofactor. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma totient_prime_product_lower {ι : Type*} (I : Finset ι) (p : ι → ℕ)
    (a : ℕ) (hp : ∀ i ∈ I, (p i).Prime) :
    a.totient*(∏ i ∈ I, (p i-1)) ≤ (a*∏ i ∈ I, p i).totient := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hrec := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
    have hprime := hp i (Finset.mem_insert_self _ _)
    calc
      _ = (a.totient*(∏ j ∈ I, (p j-1)))*(p i-1) := by ring
      _ ≤ (a*∏ j ∈ I, p j).totient*(p i-1) := Nat.mul_le_mul_right _ hrec
      _ = (a*∏ j ∈ I, p j).totient*(p i).totient := by rw [Nat.totient_prime hprime]
      _ ≤ ((a*∏ j ∈ I, p j)*p i).totient := Nat.totient_super_multiplicative _ _
      _ = _ := by congr 1; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal prime mass of finite disjoint unions of unit boxes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma reciprocalShiftWeight_nonneg {N : ℕ} (p : Fin N → ℕ) :
    0 ≤ reciprocalShiftWeight p := by unfold reciprocalShiftWeight; positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factor-count additivity and largest-factor alignment for collision pairs. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeFactor_le_largest {n p : ℕ} (hp : p ∈ n.primeFactorsList) :
    p ≤ largestPrimeFactor n := by
  have hm : p ∈ n.primeFactors := by
    change p ∈ n.primeFactorsList.toFinset
    exact List.mem_toFinset.mpr hp
  exact (Finset.le_sup (f := id) hm).trans (le_max_right _ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothSuffix
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the residual totient in an actual basic collision witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma largestPrimeFactor_le_of_prime_divisors {n z : ℕ} (hz : 1 ≤ z)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → n ≠ 0 → p ≤ z) : largestPrimeFactor n ≤ z := by
  apply max_le hz
  apply Finset.sup_le
  intro p hp
  obtain ⟨hp', hd, hn⟩ := Nat.mem_primeFactors.mp hp
  exact h p hp' hd hn

lemma prime_dvd_le_largest {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hd : p ∣ n) :
    p ≤ largestPrimeFactor n :=
  primeFactor_le_largest ((Nat.mem_primeFactorsList_iff_dvd hn hp).mpr hd)

/-- Taking a totient cannot introduce a prime larger than every prime of its
argument. This also covers `n = 0` under the existing largest-factor convention. -/
lemma largestPrimeFactor_totient_le (n : ℕ) :
    largestPrimeFactor n.totient ≤ largestPrimeFactor n := by
  by_cases hn : n = 0
  · subst n
    simp [largestPrimeFactor]
  apply largestPrimeFactor_le_of_prime_divisors (le_max_left _ _)
  intro q hq hqφ _
  have hdiv : q ∣ n*∏ p ∈ n.primeFactors, (p-1) := by
    rw [← Nat.totient_mul_prod_primeFactors]
    exact hqφ.trans (dvd_mul_right _ _)
  rcases hq.dvd_mul.mp hdiv with hqn | hqp
  · exact prime_dvd_le_largest hq hn hqn
  · obtain ⟨p, hp, hqp⟩ := hq.prime.dvd_finsetProd_iff (fun p : ℕ => p-1) |>.mp hqp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hpp.one_lt) hqp
    exact hle.trans ((Nat.sub_le _ _).trans
      (prime_dvd_le_largest hpp hn (Nat.mem_primeFactors.mp hp).2.1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordFactorization
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical finite prime-factor decomposition for the Ford coordinates. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma fordPrime_eq_get {n i : ℕ} (hi : i < n.primeFactorsList.length) :
    fordPrime n i = n.primeFactorsList.reverse[i]'(by simpa using hi) := by
  unfold fordPrime
  rw [show n.primeFactorsList.reverse[i]? = some (n.primeFactorsList.reverse[i]'(by simpa using hi)) from
    List.getElem?_eq_getElem _]
  rfl

lemma fordPrime_prime {n i : ℕ} (hi : i < n.primeFactorsList.length) : (fordPrime n i).Prime := by
  rw [fordPrime_eq_get hi]
  exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.getElem_mem _))

lemma fordPrime_antitone {n i j : ℕ} (hi : i < n.primeFactorsList.length)
    (hj : j < n.primeFactorsList.length) (hij : i ≤ j) : fordPrime n j ≤ fordPrime n i := by
  rw [fordPrime_eq_get hi,fordPrime_eq_get hj]
  exact (Nat.primeFactorsList_sorted n).reverse.getElem_ge_getElem_of_le hij

lemma fordCofactor_pos (n k : ℕ) : 0 < fordCofactor n k := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop hp))).pos

lemma ford_prefix_product {n k : ℕ} (hk : k ≤ n.primeFactorsList.length) :
    (n.primeFactorsList.reverse.take k).prod = ∏ i ∈ Finset.range k, fordPrime n i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.prod_take_succ _ _ (by simpa using hk),ih (by omega),Finset.prod_range_succ,
      fordPrime_eq_get (by omega)]

lemma ford_factorization {n k : ℕ} (hn : 0 < n) (hk : k ≤ n.primeFactorsList.length) :
    n=fordCofactor n k*∏ i ∈ Finset.range k, fordPrime n i := by
  rw [← ford_prefix_product hk,fordCofactor,mul_comm,List.prod_take_mul_prod_drop,
    List.prod_reverse,Nat.prod_primeFactorsList hn.ne']

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_QuarterPrimeCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quarter-power prime interval used in Ford’s global counting argument.
Chebyshev's library theorem suffices for the upper bound; no PNT input is used here. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The largest-prime restriction makes the logarithm of every nonempty
counting interval comparable to `log x`, uniformly in its integer denominator. -/
theorem quarter_prime_count_upper :
    ∀ᶠ x : ℝ in atTop, ∀ D : ℕ, 0 < D → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ x^(1/4 : ℝ) ≤ p ∧ ((p-1)*D : ℕ) ≤ x) →
      (Q.card : ℝ) ≤ 32*x/((D : ℝ)*Real.log x) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ)<1))
  have ht : Tendsto (fun x : ℝ => x^(1/4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ), ht.eventually (eventually_ge_atTop Y₀)] with x hx hxp
  intro D hD Q hQ
  have hD' : (0 : ℝ)<D := by exact_mod_cast hD
  have hx0 : 0<x := zero_lt_one.trans hx
  have hlogx : 0<Real.log x := Real.log_pos hx
  by_cases hne : Q.Nonempty
  · let Y := 1+x/D
    have hpY (p : ℕ) (hp : p ∈ Q) : (p : ℝ) ≤ Y := by
      have hh := hQ p hp
      have hpn := hh.1.one_lt.le
      have hval : ((p : ℝ)-1)*D ≤ x := by
        exact_mod_cast hh.2.2
      change _ ≤ 1+x/D
      have hh' := (le_div_iff₀ hD').mpr hval
      linarith
    obtain ⟨p, hp⟩ := hne
    have hlY : x^(1/4 : ℝ) ≤ Y := (hQ p hp).2.1.trans (hpY p hp)
    have hY0 : 0<Y := by dsimp [Y] <;> positivity
    have hYlarge : Y₀ ≤ Y := hxp.trans hlY
    have hlogY : (1/4 : ℝ)*Real.log x ≤ Real.log Y := by
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlY
      rw [Real.log_rpow hx0] at hh
      linarith
    have hlogYpos : 0<Real.log Y := lt_of_lt_of_le (by positivity) hlogY
    have hDx : (D : ℝ) ≤ x := by
      have hh := (hQ p hp).2.2
      have hp2 := (hQ p hp).1.two_le
      have hp1 : 1 ≤ p-1 := by omega
      have hnat : D ≤ (p-1)*D := by simpa only [one_mul] using Nat.mul_le_mul_right D hp1
      exact (by exact_mod_cast hnat : (D : ℝ) ≤ ((p-1)*D : ℕ)).trans hh
    have hYupper : Y ≤ 2*x/D := by
      change 1+x/D ≤ _
      have hone : (1 : ℝ) ≤ x/D := (le_div_iff₀ hD').mpr (by simpa using hDx)
      have he : 2*x/D = 2*(x/D) := by ring
      rw [he]
      linarith
    have hsub : Q ⊆ Nat.primesLE ⌊Y⌋₊ := by
      intro q hq
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpY q hq), (hQ q hq).1⟩
    have hcard : (Q.card : ℝ) ≤ Nat.primeCounting ⌊Y⌋₊ := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Nat.primesLE_card_eq_primeCounting _)
    have hc : Real.log 4+1 ≤ (3 : ℝ) := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
    calc
      _ ≤ (Real.log 4+1)*Y/Real.log Y := hcard.trans (hY₀ Y hYlarge)
      _ ≤ (3*(2*x/D))/((1/4 : ℝ)*Real.log x) := by
        apply div_le_div₀ (by positivity)
          ((mul_le_mul_of_nonneg_right hc hY0.le).trans (mul_le_mul_of_nonneg_left hYupper (by norm_num)))
          (by positivity) hlogY
      _ ≤ 32*x/((D : ℝ)*Real.log x) := by
        field_simp
        nlinarith
  · have hz : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeExtensionCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct totient values after adjoining a large prime to a residual preimage. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma mem_quarterPrimes {x : ℝ} {d p : ℕ} (hd : 0 < d) :
    p ∈ quarterPrimes x d ↔ p.Prime ∧ x^(1/4:ℝ) ≤ p ∧ ((p-1)*d:ℕ) ≤ x := by
  classical
  constructor
  · intro hp
    obtain ⟨hp,hx,hs⟩ := Finset.mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hp).2,hx,hs⟩
  · rintro ⟨hp,hx,hs⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor ?_,hp⟩,hx,hs⟩
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hpn : 1 ≤ p := hp.one_le
    have hle : ((p:ℝ)-1)*d ≤ x := by exact_mod_cast hs
    have hh := (le_div_iff₀ hdR).mpr hle
    linarith

lemma prime_extension_values_card (x : ℝ) (d : ℕ) :
    (primeExtensionValues x d).card ≤ 2*(quarterPrimes x d).card := by
  classical
  calc
    _ ≤ ∑ _p ∈ quarterPrimes x d,({(0:ℕ),1}:Finset ℕ).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun p _ => by simp; exact Finset.card_insert_le _ _))
    _ = _ := by simp; omega

theorem prime_extension_count_upper : ∀ᶠ x : ℝ in atTop,
    ∀ R : Finset ℕ,(∀ d ∈ R,0 < d) →
    ((R.biUnion (primeExtensionValues x)).card:ℝ) ≤
      (64*x/Real.log x)*(∑ d ∈ R,(d:ℝ)⁻¹) := by
  classical
  filter_upwards [quarter_prime_count_upper,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro R hR
  have hcount (d : ℕ) (hd : d ∈ R) :
      ((primeExtensionValues x d).card:ℝ) ≤ 64*x/(d*Real.log x) := by
    have hh := hx d (hR d hd) (quarterPrimes x d) (fun p hp => (mem_quarterPrimes (hR d hd)).mp hp)
    have hc : ((primeExtensionValues x d).card:ℝ) ≤ 2*(quarterPrimes x d).card :=
      by exact_mod_cast prime_extension_values_card x d
    calc
      _ ≤ 2*((quarterPrimes x d).card:ℝ) := hc
      _ ≤ 2*(32*x/(d*Real.log x)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ R,((primeExtensionValues x d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (R.biUnion (primeExtensionValues x)).card ≤
        ∑ d ∈ R,(primeExtensionValues x d).card)
    _ ≤ ∑ d ∈ R,64*x/(d*Real.log x) := Finset.sum_le_sum hcount
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeExtensionCoverage
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coverage of large-prime totients by their residual totient values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma totient_prime_extension_cases {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    n.totient=(p-1)*(n/p).totient ∨ n.totient=p*(n/p).totient := by
  have he : p*(n/p)=n := Nat.mul_div_cancel' hpn
  by_cases hd : p ∣ n/p
  · right
    conv_lhs => rw [← he]
    exact Nat.totient_mul_of_prime_of_dvd hp hd
  · left
    conv_lhs => rw [← he]
    exact Nat.totient_mul_of_prime_of_not_dvd hp hd

lemma totient_mem_primeExtensionValues {x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hpx : x^(1/4:ℝ) ≤ p)
    (hx : (n.totient:ℝ) ≤ x) :
    n.totient ∈ primeExtensionValues x (n/p).totient := by
  have hq : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr hq
  have hcases := totient_prime_extension_cases hp hpn
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases hcases with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  apply Finset.mem_biUnion.mpr
  refine ⟨p,(mem_quarterPrimes hd).mpr ⟨hp,hpx,hsize⟩,?_⟩
  rcases hcases with h|h <;> simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto

/-- The residual set consists of values, so repeated preimages incur no extra factor. -/
theorem large_prime_totient_count : ∀ᶠ x : ℝ in atTop,
    ∀ R Q : Finset ℕ,(∀ d ∈ R,0 < d) →
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ (n/p).totient ∈ R) →
    (Q.card:ℝ) ≤ (64*x/Real.log x)*(∑ d ∈ R,(d:ℝ)⁻¹) := by
  classical
  filter_upwards [prime_extension_count_upper] with x hx
  intro R Q hR hQ
  have hsub : Q ⊆ R.biUnion (primeExtensionValues x) := by
    intro v hv
    obtain ⟨n,p,hn,he,hp,hpn,hpx,hvx,hr⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨(n/p).totient,hr,?_⟩
    rw [← he]
    exact totient_mem_primeExtensionValues hn hp hpn hpx (by rwa [he])
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hx R hR)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCofactorStep
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of the ordered largest primes, including short factorizations. -/
noncomputable section
namespace TotientAsymptotic

lemma fordPrime_pos (n k : ℕ) : 0 < fordPrime n k := by
  by_cases hk : k < n.primeFactorsList.length
  · exact (fordPrime_prime hk).pos
  · unfold fordPrime
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
    norm_num

lemma fordCofactor_step (n k : ℕ) :
    fordCofactor n k = fordPrime n k * fordCofactor n (k+1) := by
  by_cases hk : k < n.primeFactorsList.length
  · unfold fordCofactor
    rw [List.drop_eq_getElem_cons (by simpa using hk),List.prod_cons,fordPrime_eq_get hk]
  · have hl : n.primeFactorsList.length ≤ k := Nat.le_of_not_gt hk
    have h0 : n.primeFactorsList.reverse.drop k = [] := List.drop_eq_nil_iff.mpr (by simpa using hl)
    have h1 : n.primeFactorsList.reverse.drop (k+1) = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [List.length_reverse]; omega)
    have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using hl)]
      rfl
    simp only [fordCofactor,h0,h1,List.prod_nil,hp,one_mul]

lemma fordCofactor_zero {n : ℕ} (hn : 0 < n) : fordCofactor n 0=n := by
  simp only [fordCofactor,List.drop_zero,List.prod_reverse,Nat.prod_primeFactorsList hn.ne']

lemma fordCofactor_div (n k : ℕ) :
    fordCofactor n k / fordPrime n k = fordCofactor n (k+1) := by
  conv_lhs => rw [fordCofactor_step n k]
  exact Nat.mul_div_cancel_left _ (fordPrime_pos n k)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCofactorCoordinates
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing an ordered prime prefix shifts all remaining Ford coordinates. -/
noncomputable section
namespace TotientAsymptotic

lemma fordCofactor_primeFactorsList (n k : ℕ) :
    (fordCofactor n k).primeFactorsList.reverse = n.primeFactorsList.reverse.drop k := by
  let l := n.primeFactorsList.reverse.drop k
  have hprime : ∀ p ∈ l,p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop hp))
  have hp := Nat.primeFactorsList_unique (n:=fordCofactor n k) (l:=l) rfl hprime
  have hrev : n.primeFactorsList.reverse.SortedGE := (Nat.primeFactorsList_sorted n).reverse
  have hs : l.SortedGE := (hrev.pairwise.sublist (List.drop_sublist k _)).sortedGE
  have ht := (Nat.primeFactorsList_sorted (fordCofactor n k)).reverse
  exact (hp.trans (List.reverse_perm _).symm).eq_of_sortedGE hs ht |>.symm

lemma fordCofactor_prime (n k i : ℕ) :
    fordPrime (fordCofactor n k) i = fordPrime n (k+i) := by
  unfold fordPrime
  rw [fordCofactor_primeFactorsList,List.getElem?_drop]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordLargestPrime
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading Ford prime is exactly the largest prime factor, with padding 1. -/
noncomputable section
namespace TotientAsymptotic

lemma fordPrime_zero_eq_largest (n : ℕ) : fordPrime n 0=largestPrimeFactor n := by
  apply le_antisymm
  · by_cases hi : 0 < n.primeFactorsList.length
    · rw [fordPrime_eq_get hi]
      exact primeFactor_le_largest (List.mem_reverse.mp (List.getElem_mem _))
    · have he : fordPrime n 0=1 := by
        unfold fordPrime
        rw [List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]
        rfl
      rw [he]
      exact le_max_left _ _
  · apply largestPrimeFactor_le_of_prime_divisors (fordPrime_pos n 0)
    intro p hp hpn hn
    have hm : p ∈ n.primeFactorsList.reverse :=
      List.mem_reverse.mpr ((Nat.mem_primeFactorsList_iff_dvd hn hp).mpr hpn)
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hm
    have hi' : i < n.primeFactorsList.length := by simpa using hi
    simpa only [fordPrime_eq_get hi'] using fordPrime_antitone (by omega) hi' (Nat.zero_le i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeProductValueMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct residual values of a prime prefix carry no preimage multiplicity. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma primeProductValues_positive {N : ℕ} {P : Finset (Fin N → ℕ)} {D : Finset ℕ}
    (hP : ∀ p ∈ P, ∀ i, (p i).Prime) (hD : ∀ d ∈ D, 0 < d) :
    ∀ v ∈ primeProductValues P D, 0 < v := by
  rintro v hv
  obtain ⟨⟨p,d⟩,hpd,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hp,hd⟩ := Finset.mem_product.mp hpd
  apply Nat.mul_pos (hD d hd)
  exact Nat.totient_pos.mpr (Finset.prod_pos (fun i _ => (hP p hp i).pos))

lemma primeProductValues_mass {N : ℕ} (P : Finset (Fin N → ℕ)) (D : Finset ℕ)
    (hP : ∀ p ∈ P, ∀ i, (p i).Prime) :
    (∑ v ∈ primeProductValues P D, (v:ℝ)⁻¹) ≤
      (∑ p ∈ P, reciprocalShiftWeight p)*(∑ d ∈ D,(d:ℝ)⁻¹) := by
  unfold primeProductValues
  have hh := Finset.sum_image_le_of_nonneg (s:=P.product D)
    (g:=fun z : (Fin N → ℕ) × ℕ => z.2*(∏ i, z.1 i).totient)
    (f:=fun v : ℕ => (v:ℝ)⁻¹) (fun v _ => inv_nonneg.mpr (Nat.cast_nonneg v))
  apply hh.trans
  calc
    _ = ∑ p ∈ P, ∑ d ∈ D, ((d*(∏ i, p i).totient:ℕ):ℝ)⁻¹ :=
      Finset.sum_product P D (fun z => ((z.2*(∏ i, z.1 i).totient:ℕ):ℝ)⁻¹)
    _ ≤ ∑ p ∈ P, ∑ d ∈ D, reciprocalShiftWeight p*(d:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hnat := totient_prime_product_lower Finset.univ p 1 (fun i _ => hP p hp i)
      simp only [Nat.totient_one,one_mul] at hnat
      have hpos : (0:ℝ) < (∏ i, (p i-1):ℕ) := by
        exact_mod_cast Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hP p hp i).one_lt)
      have hrec := inv_anti₀ hpos (Nat.cast_le.mpr hnat)
      apply Finset.sum_le_sum
      intro d _
      simp only [Nat.cast_mul,mul_inv_rev]
      exact mul_le_mul_of_nonneg_right hrec (inv_nonneg.mpr (Nat.cast_nonneg d))
    _ = _ := by simp only [← Finset.mul_sum,← Finset.sum_mul]

/-- Count values with a large leading prime after encoding the remaining
prefix and its cofactor by their distinct totient values. -/
theorem large_prime_product_value_count : ∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ, ∀ P : Finset (Fin N → ℕ), ∀ D Q : Finset ℕ,
      (∀ p ∈ P, ∀ i, (p i).Prime) → (∀ d ∈ D, 0 < d) →
      (∀ v ∈ Q, ∃ n p : ℕ, 0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
        x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ (n/p).totient ∈ primeProductValues P D) →
      (Q.card:ℝ) ≤ (64*x/Real.log x)*
        (∑ p ∈ P,reciprocalShiftWeight p)*(∑ d ∈ D,(d:ℝ)⁻¹) := by
  filter_upwards [large_prime_totient_count,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro N P D Q hP hD hQ
  have hh := hx (primeProductValues P D) Q (primeProductValues_positive hP hD) hQ
  apply hh.trans
  have hc : 0 ≤ 64*x/Real.log x := by
    exact div_nonneg (by positivity) (Real.log_pos hx1).le
  have hm := mul_le_mul_of_nonneg_left (primeProductValues_mass P D hP) hc
  simpa only [mul_assoc] using hm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictCofactorSplit
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact totient factorization at a strict gap in the ordered prime list. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordCofactor_largest_exact (n k : ℕ) :
    largestPrimeFactor (fordCofactor n k) = fordPrime n k := by
  rw [← fordPrime_zero_eq_largest,fordCofactor_prime,Nat.add_zero]

theorem strict_cofactor_coprime {n k : ℕ} (hk : 0 < k)
    (hklen : k ≤ n.primeFactorsList.length)
    (hgap : fordPrime n k < fordPrime n (k-1)) :
    (fordCofactor n k).Coprime (∏ i ∈ Finset.range k, fordPrime n i) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro i hi
  have hi := Finset.mem_range.mp hi
  have hip := fordPrime_prime (show i < n.primeFactorsList.length by omega)
  apply Nat.Coprime.symm
  apply hip.coprime_iff_not_dvd.mpr
  intro hd
  have hle := prime_dvd_le_largest hip (fordCofactor_pos n k).ne' hd
  rw [fordCofactor_largest_exact] at hle
  have horder := fordPrime_antitone (show i < n.primeFactorsList.length by omega)
    (show k-1 < n.primeFactorsList.length by omega) (show i ≤ k-1 by omega)
  omega

theorem strict_cofactor_totient {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hklen : k ≤ n.primeFactorsList.length)
    (hgap : fordPrime n k < fordPrime n (k-1)) :
    n.totient = (fordCofactor n k).totient *
      (∏ i ∈ Finset.range k, fordPrime n i).totient := by
  have hcop := strict_cofactor_coprime hk hklen hgap
  conv_lhs => rw [ford_factorization hn hklen]
  exact Nat.totient_mul hcop

lemma fordCofactor_comp (n i j : ℕ) :
    fordCofactor (fordCofactor n i) j = fordCofactor n (i+j) := by
  change ((fordCofactor n i).primeFactorsList.reverse.drop j).prod =
    (n.primeFactorsList.reverse.drop (i+j)).prod
  rw [fordCofactor_primeFactorsList,List.drop_drop]

lemma fordCofactor_length (n i : ℕ) :
    (fordCofactor n i).primeFactorsList.length = n.primeFactorsList.length-i := by
  have hh := congrArg List.length (fordCofactor_primeFactorsList n i)
  simpa only [List.length_reverse,List.length_drop] using hh

/-- The leading prime may have either totient-extension branch. After its
removal, the strict boundary still gives an exact residual-value encoding. -/
theorem strict_gap_residual_totient {n j : ℕ} (hn : 0 < n) (hj : 0 < j)
    (hjlen : j ≤ n.primeFactorsList.length)
    (hgap : fordPrime n j < fordPrime n (j-1)) :
    (n/fordPrime n 0).totient = (fordCofactor n j).totient *
      (∏ i : Fin (j-1), fordPrime n (i.val+1)).totient := by
  have he : n/fordPrime n 0=fordCofactor n 1 := by
    simpa only [fordCofactor_zero hn,Nat.zero_add] using fordCofactor_div n 0
  rw [he]
  by_cases hj1 : j=1
  · subst j
    simp
  · have hk : 0 < j-1 := by omega
    have hklen : j-1 ≤ (fordCofactor n 1).primeFactorsList.length := by
      rw [fordCofactor_length]
      omega
    have hs : fordPrime (fordCofactor n 1) (j-1) <
        fordPrime (fordCofactor n 1) (j-1-1) := by
      simp only [fordCofactor_prime]
      convert hgap using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> omega)
    have hh := strict_cofactor_totient (fordCofactor_pos n 1) hk hklen hs
    rw [fordCofactor_comp,show 1+(j-1)=j by omega] at hh
    rw [Fin.prod_univ_eq_prod_range (fun i => fordPrime n (i+1))]
    simpa only [fordCofactor_prime,Nat.add_comm 1] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallTerminalPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded terminal coordinate supplies an exact smooth residual split. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_prime_le_exp_exp {n j : ℕ} {t : ℝ} (_ht : 0 ≤ t)
    (hj : fordPrimeCoordinate n j ≤ t) :
    (fordPrime n j:ℝ) ≤ Real.exp (Real.exp t) := by
  by_cases hp : fordPrime n j=1
  · rw [hp,Nat.cast_one]
    exact Real.one_le_exp (Real.exp_pos _).le
  have hp1 : (1:ℝ) < fordPrime n j := by
    exact_mod_cast (show 1 < fordPrime n j from lt_of_le_of_ne (fordPrime_pos n j) (Ne.symm hp))
  have hlog : 0 < Real.log (fordPrime n j:ℝ) := Real.log_pos hp1
  have hh : Real.log (Real.log (fordPrime n j:ℝ)) ≤ t := (le_max_right _ _).trans hj
  have he : Real.log (fordPrime n j:ℝ) ≤ Real.exp t :=
    (Real.log_le_iff_le_exp hlog).mp hh
  exact (Real.log_le_iff_le_exp (zero_lt_one.trans hp1)).mp he

lemma small_terminal_smooth {n j : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcur : fordPrimeCoordinate n j ≤ t) :
    (largestPrimeFactor (fordCofactor n j).totient:ℝ) ≤ Real.exp (Real.exp t) := by
  have hh := (largestPrimeFactor_totient_le (fordCofactor n j)).trans_eq (fordCofactor_largest_exact n j)
  exact (Nat.cast_le.mpr hh).trans (ford_prime_le_exp_exp ht hcur)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TerminalPrefixMassCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain an arbitrary restriction on the prime prefix while counting a
terminal strip through its distinct residual totients. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem terminal_prefix_mass_count_oai : ∃ D : ℝ,0 < D ∧
    ∀ᶠ x : ℝ in atTop,∀ K k : ℕ,∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v∈Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      K+1 ≤ (n v).primeFactorsList.length ∧
      fordPrime (n v) (K+1) < fordPrime (n v) K ∧
      fordPrimeCoordinate (n v) (K+1) ≤ (k:ℝ)+1) →
    (Q.card:ℝ) ≤ D*(x/Real.log x)*
      (∑ p∈Q.image (fun v => fordPrefixPrimes (n v) K),reciprocalShiftWeight p)*
      Real.exp (10*(Real.log ((k:ℝ)+5))^2) := by
  obtain ⟨D,hD,hres⟩ := smooth_terminal_mass_bound
  refine ⟨64*D,by positivity,?_⟩
  filter_upwards [large_prime_product_value_count,eventually_gt_atTop (1:ℝ)]
    with x hx hx1
  intro K k Q n hQ
  let P := Q.image (fun v => fordPrefixPrimes (n v) K)
  let R := Q.image (fun v => (fordCofactor (n v) (K+1)).totient)
  have hRpos (d) (hd : d∈R) : 0 < d := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.totient_pos.mpr (fordCofactor_pos _ _)
  have hRmass : (∑ d∈R,(d:ℝ)⁻¹) ≤ D*Real.exp (10*(Real.log ((k:ℝ)+5))^2) := by
    apply hres k (by positivity) R
    intro d hd
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hd
    exact ⟨⟨fordCofactor (n v) (K+1),fordCofactor_pos _ _,rfl⟩,
      small_terminal_smooth (by positivity) (hQ v hv).2.2.2.2.2.2⟩
  have hh := hx K P R Q (by
    intro p hp i
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    apply fordPrime_prime
    have hlen := (hQ v hv).2.2.2.2.1
    have := i.isLt
    omega) hRpos (by
    intro v hv
    obtain ⟨hn,hφ,hhead,hvx,hlen,hgap,_⟩ := hQ v hv
    refine ⟨n v,fordPrime (n v) 0,hn,hφ,fordPrime_prime (by omega),?_,hhead,hvx,?_⟩
    · have he := fordCofactor_step (n v) 0
      rw [fordCofactor_zero hn] at he
      exact ⟨fordCofactor (n v) 1,he⟩
    · apply Finset.mem_image.mpr
      refine ⟨(fordPrefixPrimes (n v) K,(fordCofactor (n v) (K+1)).totient),
        Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,
          Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩,?_⟩
      have he := (strict_gap_residual_totient (n:=n v) (j:=K+1) hn (by omega) hlen hgap).symm
      change (fordCofactor (n v) (K+1)).totient *
        (∏ i : Fin K,fordPrime (n v) (i.val+1)).totient = _
      rw [Fin.prod_univ_eq_prod_range (fun i => fordPrime (n v) (i+1))] at he ⊢
      simpa only [Nat.add_sub_cancel] using he)
  apply hh.trans
  have hcoef : 0 ≤ (64*x/Real.log x)*(∑ p∈P,reciprocalShiftWeight p) :=
    mul_nonneg (div_nonneg (by positivity) (Real.log_pos hx1).le)
      (Finset.sum_nonneg (fun p _ => reciprocalShiftWeight_nonneg p))
  have hh' := mul_le_mul_of_nonneg_left hRmass hcoef
  convert hh' using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [P] <;> ring)

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.terminal_prefix_mass_count_oai := @OAI.TotientAsymptotic.terminal_prefix_mass_count_oai
