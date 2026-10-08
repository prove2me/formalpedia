-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_typical_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:36:23.018866+00:00
-- url     : https://prove2.me/submissions/5548f35b-0692-41ca-86e2-bae310736c86

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_mixed_double_estimate
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_mixed_mean_numeric

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped _root_.BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]



omit [DecidableEq α] [LinearOrder ι] in
@[simp] theorem mem_survivors {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α} :
    x ∈ survivors C P bad ↔ x ∈ C ∧ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [survivors]











instance decidableResidueBad (a : ℕ → ℕ) (p n : ℕ) : Decidable (residueBad a p n) :=
  inferInstanceAs (Decidable (n % p = a p % p))






end NumberTheoryLean.SievePartition

end

section

namespace NumberTheoryLean.SieveTree

open scoped _root_.BigOperators

variable {V : Type*} [DecidableEq V]








end NumberTheoryLean.SieveTree

end

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped _root_.BigOperators
open _root_.OAI.Erdos970.NumberTheoryLean.SievePartition

















end NumberTheoryLean.ResidueSieveTree

end

section

namespace ErdosInverseCounts
open _root_.OAI.Erdos970.NumberTheoryLean _root_.OAI.Erdos970.NumberTheoryLean.SievePartition









end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression






end ErdosAlignedProgression

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.LargePrimeDeletion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped _root_.BigOperators






@[simp] theorem mem_deletionCell {C : Finset ℕ} {a : ℤ} {q i : ℕ} :
    i ∈ deletionCell C a q ↔ i ∈ C ∧ (q : ℤ) ∣ a + i := by
  classical
  simp [deletionCell]







@[simp] theorem mem_cutoffSurvivors {Y z i : ℕ} {residue : ℕ → ℕ} :
    i ∈ cutoffSurvivors Y z residue ↔
      i < Y ∧ ∀ p, p.Prime → p ≤ z → i % p ≠ residue p % p := by
  classical
  simp only [cutoffSurvivors, SievePartition.mem_survivors, Finset.mem_range,
    mem_cutoffPrimes, SievePartition.residueBad]
  tauto





@[simp] theorem mem_coprimeOffsets {Y n i : ℕ} {a : ℤ} :
    i ∈ coprimeOffsets Y n a ↔ i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  simp [coprimeOffsets]









end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.IntervalBoundingSieve
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped _root_.BigOperators
















@[simp] theorem cutoffProduct_primeFactors (z : ℕ) :
    (cutoffProduct z).primeFactors = LargePrimeDeletion.cutoffPrimes z := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1


end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped _root_.BigOperators


@[simp] theorem elementarySum_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    elementarySum P g 0 = 1 := by simp [elementarySum]











@[simp] theorem densityPolynomial_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial 0 P g = 1 := by simp [densityPolynomial]









end NumberTheoryLean.BonferroniDensity

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.DisjointBlockExpansion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped _root_.BigOperators


@[simp] theorem mem_blockChoices {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {choice : ∀ j ∈ B, Finset ℕ} :
    choice ∈ blockChoices B blocks ↔ ∀ j (hj : j ∈ B), choice j hj ⊆ blocks j := by
  classical
  simp only [blockChoices, Finset.mem_pi, Finset.mem_powerset]






















@[simp] theorem truncatedCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    truncatedCoefficient m T ≠ 0 ↔ T.card ≤ m := by
  unfold truncatedCoefficient
  split_ifs <;> simp_all

@[simp] theorem layerCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    layerCoefficient m T ≠ 0 ↔ T.card = m := by
  unfold layerCoefficient
  split_ifs <;> simp_all


























end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.SquarefreeHarmonic
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius




























end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped _root_.BigOperators


@[simp] theorem mem_squarefreeUpTo {R d : ℕ} :
    d ∈ squarefreeUpTo R ↔ 1 ≤ d ∧ d ≤ R ∧ Squarefree d := by
  classical
  simp only [squarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto
















end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.PrimeDensityBlocks
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped _root_.BigOperators


@[simp] theorem mem_dyadicPrimes {n p : ℕ} :
    p ∈ dyadicPrimes n ↔ n ≤ p ∧ p < 2 * n ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto






@[simp] theorem mem_geometricPrimes {j p : ℕ} :
    p ∈ geometricPrimes j ↔ 2 ^ (2 ^ j) ≤ p ∧ p < 2 ^ (2 ^ (j + 1)) ∧ p.Prime := by
  simp only [geometricPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto





















end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LocalFactors
namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations


@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]



@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowers
namespace OAI

/-! The total reciprocal contribution of higher prime powers is finite.
The modulus-one specialization of the prime-power series bounds
the finite hyperbola error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszPrimePowerWeight_nonneg (n : ℕ) : 0 ≤ halaszPrimePowerWeight n := by
  unfold halaszPrimePowerWeight
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg



lemma halaszPrimePowerConstant_nonneg : 0 ≤ halaszPrimePowerConstant :=
  tsum_nonneg (fun n => div_nonneg (halaszPrimePowerWeight_nonneg n) (Nat.cast_nonneg _))



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.ComplexConjugate

lemma mrt_local_euler_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹‖ ≤ Real.exp (z.re + ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hnz : 1 - z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one] at hz1
    exact lt_irrefl _ hz1
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)).mpr
    linarith
  have hrem : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hre : (Complex.log (1 - z)⁻¹).re ≤ z.re + ‖z‖ ^ 2 := by
    have h := (Complex.re_le_norm (Complex.log (1 - z)⁻¹ - z)).trans hrem
    rw [Complex.sub_re] at h
    linarith
  calc
    _ = Real.exp (Complex.log (1 - z)⁻¹).re := by
      rw [← Complex.norm_exp, Complex.exp_log (inv_ne_zero hnz)]
    _ ≤ _ := Real.exp_le_exp.mpr hre


lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _


lemma mrtPrimeEulerTerm_norm_le (b : ℕ → ℂ) (t : ℝ) {p : ℕ}
    (_hp : 0 < p) (hb : ‖b p‖ ≤ 1) :
    ‖mrtPrimeEulerTerm b t p‖ ≤ (1 : ℝ) / p := by
  rw [mrtPrimeEulerTerm, norm_div, norm_mul, norm_conj,
    mrtArchimedeanTwist_norm, mul_one, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)

lemma mrtPrimeEulerTerm_re (b : ℕ → ℂ) (t : ℝ) (p : ℕ) :
    (mrtPrimeEulerTerm b t p).re = (b p * conj (mrtArchimedeanTwist t p)).re / p := by
  change (b p * conj (mrtArchimedeanTwist t p) / ((p : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re]

/-- The finite Euler product retains the full pretentious-distance gain.
The remaining prime-square error is absolutely summable. -/
theorem mrt_finite_euler_distance_bound (b : ℕ → ℂ)
    (hb : ∀ n : ℕ, 0 < n → ‖b n‖ ≤ 1) (t : ℝ) (N : ℕ) :
    ‖∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm b t p)⁻¹‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance b (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  have hz (p : ℕ) (hp : p ∈ primesUpTo N) : ‖mrtPrimeEulerTerm b t p‖ ≤ 1 / 2 := by
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    exact (mrtPrimeEulerTerm_norm_le b t hprime.pos (hb p hprime.pos)).trans
      (one_div_le_one_div_of_le (by norm_num) hp2)
  have hs : (∑ p ∈ primesUpTo N,
      ((mrtPrimeEulerTerm b t p).re + (1 : ℝ) / (p : ℝ) ^ 2)) =
      (∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance b (mrtArchimedeanTwist t) N +
          ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
    rw [sum_add_distrib, squaredDistance, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    rw [mrtPrimeEulerTerm_re]
    ring
  rw [norm_prod, ← hs, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _
    exact norm_nonneg _
  · intro p hp
    apply (mrt_local_euler_bound (hz p hp)).trans
    apply Real.exp_le_exp.mpr
    apply add_le_add le_rfl
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ ≤ ((1 : ℝ) / p) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (mrtPrimeEulerTerm_norm_le b t hprime.pos
          (hb p hprime.pos)) 2
      _ = _ := by simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandCancellation
namespace OAI

/-! The elementary band cancellation in corrected MRT, Appendix A,
Lemma A.8 and equation (A.12). -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.ComplexConjugate

lemma mrt_exp_sub_square_monotone : Monotone (fun x : ℝ => Real.exp x - x ^ 2) := by
  apply monotone_of_hasDerivAt_nonneg
    (f' := fun x => Real.exp x - 2 * x)
  · intro x
    convert (preTransparency := .instances) (Real.hasDerivAt_exp x).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      first | rfl | norm_num
  · intro x
    exact sub_nonneg.mpr Real.two_mul_le_exp

/-- Corrected MRT Lemma A.8, proved using the monotonicity of
`exp x - x²` rather than a second derivative at a square root. -/
theorem mrt_exp_cos_inequality (a θ : ℝ) :
    Real.exp a + Real.exp (-a) - 2 * Real.cos θ ≤
      Real.exp (Real.sqrt (a ^ 2 + θ ^ 2)) := by
  have hs : 0 ≤ a ^ 2 + θ ^ 2 := by positivity
  have ha : |a| ≤ Real.sqrt (a ^ 2 + θ ^ 2) :=
    Real.le_sqrt_of_sq_le (by rw [sq_abs]; nlinarith [sq_nonneg θ])
  have hm := mrt_exp_sub_square_monotone ha
  change Real.exp |a| - |a| ^ 2 ≤
    Real.exp (Real.sqrt (a ^ 2 + θ ^ 2)) - Real.sqrt (a ^ 2 + θ ^ 2) ^ 2 at hm
  rw [sq_abs, Real.sq_sqrt hs] at hm
  have he : Real.exp a + Real.exp (-a) ≤ Real.exp |a| + 1 := by
    by_cases ha0 : 0 ≤ a
    · rw [abs_of_nonneg ha0]
      have hh : Real.exp (-a) ≤ 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -a ≤ 0)
      linarith
    · rw [abs_of_neg (lt_of_not_ge ha0)]
      have hh : Real.exp a ≤ 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (le_of_not_ge ha0)
      linarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
  linarith

lemma mrt_exp_difference_square (z : ℂ) :
    ‖Complex.exp (z / 2) - Complex.exp (-z / 2)‖ ^ 2 =
      Real.exp z.re + Real.exp (-z.re) - 2 * Real.cos z.im := by
  have hp : z / 2 + conj (-z / 2) = (z.im : ℂ) * Complex.I := by
    simp only [map_div₀, map_neg, map_ofNat]
    apply Complex.ext
    · simp
      ring
    · simp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.norm_exp, Complex.norm_exp, ← Complex.exp_conj, ← Complex.exp_add, hp]
  have h1 : Real.exp (z / 2).re ^ 2 = Real.exp z.re := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp
    ring
  have h2 : Real.exp (-z / 2).re ^ 2 = Real.exp (-z.re) := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp
    ring
  rw [h1, h2]
  simp [Complex.exp_re]

theorem mrt_exp_difference_bound (z : ℂ) :
    ‖Complex.exp (z / 2) - Complex.exp (-z / 2)‖ ≤ Real.exp (‖z‖ / 2) := by
  have hsq := mrt_exp_cos_inequality z.re z.im
  rw [← Complex.norm_eq_sqrt_sq_add_sq, ← mrt_exp_difference_square] at hsq
  have he : Real.exp (‖z‖ / 2) ^ 2 = Real.exp ‖z‖ := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← he] at hsq
  nlinarith [norm_nonneg (Complex.exp (z / 2) - Complex.exp (-z / 2)),
    Real.exp_pos (‖z‖ / 2)]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandEuler
namespace OAI

/-! Exact finite Euler-product bounds for inclusion-exclusion over prime
bands.  Each nonempty-band factor pays a square root of its Euler product,
with only the summable prime-square error remaining. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.ComplexConjugate

lemma mrt_local_euler_log_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 - z)⁻¹‖ ≤ ‖z‖ + ‖z‖ ^ 2 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)).mpr
    linarith
  have hr : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  calc
    _ = ‖(Complex.log (1 - z)⁻¹ - z) + z‖ := by congr 1; ring
    _ ≤ ‖Complex.log (1 - z)⁻¹ - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ _ := by linarith

lemma mrt_exp_sub_one_bound (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤
      Real.sqrt ‖Complex.exp z‖ * Real.exp (‖z‖ / 2) := by
  have hf : Complex.exp z - 1 = Complex.exp (z / 2) *
      (Complex.exp (z / 2) - Complex.exp (-z / 2)) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add,
      show z / 2 + z / 2 = z by ring,
      show z / 2 + -z / 2 = 0 by ring, Complex.exp_zero]
  rw [hf, norm_mul]
  have he : ‖Complex.exp (z / 2)‖ = Real.sqrt ‖Complex.exp z‖ := by
    rw [Complex.norm_exp, Complex.norm_exp, Complex.div_ofNat_re, Real.exp_half]
  rw [he]
  exact mul_le_mul_of_nonneg_left (mrt_exp_difference_bound z) (Real.sqrt_nonneg _)

lemma mrt_euler_block_exp {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    Complex.exp (∑ i ∈ S, Complex.log (1 - z i)⁻¹) =
      ∏ i ∈ S, (1 - z i)⁻¹ := by
  rw [Complex.exp_sum]
  apply prod_congr rfl
  intro i hi
  apply Complex.exp_log
  apply inv_ne_zero
  intro he
  have hez : z i = 1 := (sub_eq_zero.mp he).symm
  have := hz i hi
  simp only [hez, norm_one] at this
  norm_num at this

theorem mrt_euler_block_difference_bound {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    ‖(∏ i ∈ S, (1 - z i)⁻¹) - 1‖ ≤
      Real.sqrt ‖∏ i ∈ S, (1 - z i)⁻¹‖ *
        Real.exp ((∑ i ∈ S, (‖z i‖ + ‖z i‖ ^ 2)) / 2) := by
  have he := mrt_euler_block_exp S z hz
  have hb := mrt_exp_sub_one_bound (∑ i ∈ S, Complex.log (1 - z i)⁻¹)
  rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  exact (norm_sum_le _ _).trans (sum_le_sum fun i hi => mrt_local_euler_log_bound (hz i hi))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandProducts
namespace OAI

/-! Multiplication of the band bounds preserves a single square-root
Euler factor.  Pairwise disjointness removes every repeated prime cost. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.Classical

lemma mrt_euler_block_bound {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    ‖∏ i ∈ S, (1 - z i)⁻¹‖ ≤
      Real.sqrt ‖∏ i ∈ S, (1 - z i)⁻¹‖ *
        Real.exp ((∑ i ∈ S, (‖z i‖ + ‖z i‖ ^ 2)) / 2) := by
  let L : ℂ := ∑ i ∈ S, Complex.log (1 - z i)⁻¹
  have he : Complex.exp L = ∏ i ∈ S, (1 - z i)⁻¹ := mrt_euler_block_exp S z hz
  have hnorm : ‖∏ i ∈ S, (1 - z i)⁻¹‖ = Real.exp L.re := by
    rw [← he, Complex.norm_exp]
  have hL : L.re ≤ ∑ i ∈ S, (‖z i‖ + ‖z i‖ ^ 2) :=
    (Complex.re_le_norm L).trans ((norm_sum_le _ _).trans
      (sum_le_sum fun i hi => mrt_local_euler_log_bound (hz i hi)))
  rw [hnorm, ← Real.exp_half, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem mrt_band_product_bound {ι κ : Type*} (R : Finset ι) (J : Finset κ)
    (P : κ → Finset ι) (z : ι → ℂ)
    (hR : ∀ i ∈ R, ‖z i‖ ≤ 1 / 2)
    (hP : ∀ j ∈ J, ∀ i ∈ P j, ‖z i‖ ≤ 1 / 2) :
    ‖(∏ i ∈ R, (1 - z i)⁻¹) *
        ∏ j ∈ J, ((∏ i ∈ P j, (1 - z i)⁻¹) - 1)‖ ≤
      Real.sqrt ‖(∏ i ∈ R, (1 - z i)⁻¹) * ∏ j ∈ J, ∏ i ∈ P j, (1 - z i)⁻¹‖ *
        Real.exp (((∑ i ∈ R, (‖z i‖ + ‖z i‖ ^ 2)) +
          ∑ j ∈ J, ∑ i ∈ P j, (‖z i‖ + ‖z i‖ ^ 2)) / 2) := by
  have hb := mrt_euler_block_bound R z hR
  have hp := Finset.prod_le_prod
    (fun j (_ : j ∈ J) => norm_nonneg ((∏ i ∈ P j, (1 - z i)⁻¹) - 1))
    (fun j hj => mrt_euler_block_difference_bound (P j) z (hP j hj))
  rw [norm_mul, norm_prod (f := fun j => (∏ i ∈ P j, (1 - z i)⁻¹) - 1)]
  calc
    _ ≤ (Real.sqrt ‖∏ i ∈ R, (1 - z i)⁻¹‖ *
          Real.exp ((∑ i ∈ R, (‖z i‖ + ‖z i‖ ^ 2)) / 2)) *
        ∏ j ∈ J, (Real.sqrt ‖∏ i ∈ P j, (1 - z i)⁻¹‖ *
          Real.exp ((∑ i ∈ P j, (‖z i‖ + ‖z i‖ ^ 2)) / 2)) := by
      exact mul_le_mul hb hp (prod_nonneg fun _ _ => norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    _ = _ := by
      rw [prod_mul_distrib, ← Real.sqrt_prod J (fun _ _ => norm_nonneg _),
        ← Real.exp_sum, ← norm_prod, norm_mul, Real.sqrt_mul (norm_nonneg _),
        ← sum_div]
      rw [show ((∑ i ∈ R, (‖z i‖ + ‖z i‖ ^ 2)) +
          ∑ j ∈ J, ∑ i ∈ P j, (‖z i‖ + ‖z i‖ ^ 2)) / 2 =
          (∑ i ∈ R, (‖z i‖ + ‖z i‖ ^ 2)) / 2 +
          (∑ j ∈ J, ∑ i ∈ P j, (‖z i‖ + ‖z i‖ ^ 2)) / 2 by ring,
        Real.exp_add]
      ring

/-- The complement and all disjoint bands partition the original finite
Euler product, so the cost contains each prime exactly once. -/
theorem mrt_partitioned_euler_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J : Finset κ)
    (P : κ → Finset ι) (z : ι → ℂ)
    (hsub : ∀ j ∈ J, P j ⊆ S) (hdis : Set.PairwiseDisjoint (J : Set κ) P)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    ‖(∏ i ∈ S \ J.biUnion P, (1 - z i)⁻¹) *
        ∏ j ∈ J, ((∏ i ∈ P j, (1 - z i)⁻¹) - 1)‖ ≤
      Real.sqrt ‖∏ i ∈ S, (1 - z i)⁻¹‖ *
        Real.exp ((∑ i ∈ S, (‖z i‖ + ‖z i‖ ^ 2)) / 2) := by
  have hU : J.biUnion P ⊆ S := by
    intro i hi
    obtain ⟨j, hj, hip⟩ := mem_biUnion.mp hi
    exact hsub j hj hip
  have hp := mrt_band_product_bound (S \ J.biUnion P) J P z
    (fun i hi => hz i (mem_sdiff.mp hi).1) (fun j hj i hi => hz i (hsub j hj hi))
  rw [← prod_biUnion hdis, prod_sdiff hU, ← sum_biUnion hdis, sum_sdiff hU] at hp
  exact hp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandIdentity
namespace OAI

/-! Exact inclusion-exclusion for a finite Euler product partitioned into
disjoint prime bands.  No analytic estimate is used in this identity. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_band_complement {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J I : Finset κ)
    (P : κ → Finset ι) (hI : I ⊆ J) (hsub : ∀ j ∈ J, P j ⊆ S)
    (hdis : Set.PairwiseDisjoint (J : Set κ) P) :
    S \ I.biUnion P = (S \ J.biUnion P) ∪ (J \ I).biUnion P := by
  ext p
  constructor
  · intro hp
    rcases mem_sdiff.mp hp with ⟨hpS, hpI⟩
    by_cases hpJ : p ∈ J.biUnion P
    · obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hpJ
      have hjI : j ∉ I := fun hi => hpI (mem_biUnion.mpr ⟨j, hi, hpj⟩)
      exact mem_union_right _ (mem_biUnion.mpr ⟨j, mem_sdiff.mpr ⟨hj, hjI⟩, hpj⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hpS, hpJ⟩)
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · rcases mem_sdiff.mp hp with ⟨hpS, hpJ⟩
      refine mem_sdiff.mpr ⟨hpS, ?_⟩
      intro hpI
      obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hpI
      exact hpJ (mem_biUnion.mpr ⟨j, hI hj, hpj⟩)
    · obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp
      rcases mem_sdiff.mp hj with ⟨hjJ, hjI⟩
      refine mem_sdiff.mpr ⟨hsub j hjJ hpj, ?_⟩
      intro hpI
      obtain ⟨i, hi, hpi⟩ := mem_biUnion.mp hpI
      have hne : i ≠ j := fun he => hjI (he ▸ hi)
      exact Finset.disjoint_left.mp (hdis (hI hi) hjJ hne) hpi hpj

lemma mrt_band_complement_disjoint {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J I : Finset κ)
    (P : κ → Finset ι) :
    Disjoint (S \ J.biUnion P) ((J \ I).biUnion P) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp'
  exact (mem_sdiff.mp hp).2 (mem_biUnion.mpr ⟨j, (mem_sdiff.mp hj).1, hpj⟩)

theorem mrt_band_complement_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J I : Finset κ)
    (P : κ → Finset ι) (a : ι → ℂ) (hI : I ⊆ J)
    (hsub : ∀ j ∈ J, P j ⊆ S) (hdis : Set.PairwiseDisjoint (J : Set κ) P) :
    (∏ p ∈ S \ I.biUnion P, a p) =
      (∏ p ∈ S \ J.biUnion P, a p) * ∏ j ∈ J \ I, ∏ p ∈ P j, a p := by
  rw [mrt_band_complement S J I P hI hsub hdis,
    prod_union (mrt_band_complement_disjoint S J I P)]
  congr 1
  exact prod_biUnion (fun i hi j hj hij =>
    hdis (mem_sdiff.mp hi).1 (mem_sdiff.mp hj).1 hij)

/-- The alternating masked Euler products factor exactly into one
unrestricted complement and one nonempty factor for each band. -/
theorem mrt_euler_inclusion_exclusion {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J : Finset κ)
    (P : κ → Finset ι) (a : ι → ℂ)
    (hsub : ∀ j ∈ J, P j ⊆ S) (hdis : Set.PairwiseDisjoint (J : Set κ) P) :
    (∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card * ∏ p ∈ S \ I.biUnion P, a p) =
      (∏ p ∈ S \ J.biUnion P, a p) *
        ∏ j ∈ J, ((∏ p ∈ P j, a p) - 1) := by
  rw [prod_sub, mul_sum]
  apply sum_congr rfl
  intro I hI
  rw [mrt_band_complement_product S J I P a (mem_powerset.mp hI) hsub hdis,
    prod_const_one, mul_one]
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare
namespace OAI

/-! The normalized dyadic Dirichlet-polynomial mean-value estimate used in
corrected MRT Appendix A.  The coefficient bound is completely arbitrary. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators



lemma mrt_line_one_term (b : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term b (1 + (t : ℂ) * Complex.I) n =
      b n / (n : ℂ) * Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
    Complex.cpow_add _ _ hnC, Complex.cpow_neg_one,
    Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  rw [div_eq_mul_inv, mul_assoc]
  congr 1
  congr 1
  push_cast
  ring_nf



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiplicativeReduction
namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical








@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]






@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := if_neg hn.ne'




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalFactors
namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators





lemma mrtPrimeAvoids_union (P Q : Finset ℕ) (n : ℕ) :
    mrtPrimeAvoids (P ∪ Q) n ↔ mrtPrimeAvoids P n ∧ mrtPrimeAvoids Q n := by
  simp only [mrtPrimeAvoids, mem_union]
  aesop

lemma mrtPrimeMask_union (P Q : Finset ℕ) (n : ℕ) :
    mrtPrimeMask (P ∪ Q) n = mrtPrimeMask P n * mrtPrimeMask Q n := by
  simp only [mrtPrimeMask, mrtPrimeAvoids_union]
  by_cases hp : mrtPrimeAvoids P n <;> by_cases hq : mrtPrimeAvoids Q n <;> simp [hp, hq]

lemma mrtPrimeAvoids_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    mrtPrimeAvoids P (m * n) ↔ mrtPrimeAvoids P m ∧ mrtPrimeAvoids P n := by
  simp only [mrtPrimeAvoids]
  constructor
  · intro h
    exact ⟨fun p hp hpm => h p hp (dvd_mul_of_dvd_left hpm n),
      fun p hp hpn => h p hp (dvd_mul_of_dvd_right hpn m)⟩
  · rintro ⟨hm, hn⟩ p hp hdiv
    exact ((hP p hp).dvd_mul.mp hdiv).elim (hm p hp) (hn p hp)

lemma mrtPrimeMask_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    mrtPrimeMask P (m * n) = mrtPrimeMask P m * mrtPrimeMask P n := by
  simp only [mrtPrimeMask, mrtPrimeAvoids_mul P hP]
  by_cases hm : mrtPrimeAvoids P m <;> by_cases hn : mrtPrimeAvoids P n <;> simp [hm, hn]

lemma mrtPrimeMask_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    mrtPrimeMask P 1 = 1 := by
  unfold mrtPrimeMask
  apply if_pos
  intro p hp hdiv
  exact (hP p hp).ne_one (Nat.eq_one_of_dvd_one hdiv)

lemma mrtPrimeMask_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hp : p.Prime) : mrtPrimeMask P p = if p ∈ P then 0 else 1 := by
  have he : mrtPrimeAvoids P p ↔ p ∉ P := by
    constructor
    · intro h hmem
      exact h p hmem (dvd_refl p)
    · intro h q hq hqp
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp
      exact h (heq ▸ hq)
  simp only [mrtPrimeMask, he]
  split_ifs <;> simp_all

lemma mrtPrimeMask_biUnion {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) :
    mrtPrimeMask (J.biUnion P) n = ∏ j ∈ J, mrtPrimeMask (P j) n := by
  induction J using Finset.induction_on with
  | empty => simp [mrtPrimeMask, mrtPrimeAvoids]
  | @insert j J hj ih =>
    rw [biUnion_insert, mrtPrimeMask_union, prod_insert hj, ih]

lemma mrtTypical_prod {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) :
    (∏ j ∈ J, (1 - mrtPrimeMask (P j) n)) = if mrtTypical J P n then 1 else 0 := by
  induction J using Finset.induction_on with
  | empty => simp [mrtTypical]
  | @insert j J hj ih =>
    rw [prod_insert hj, ih]
    have he : mrtTypical (insert j J) P n ↔
        (¬ mrtPrimeAvoids (P j) n) ∧ mrtTypical J P n := by
      simp only [mrtTypical, mem_insert, mrtPrimeAvoids]
      push Not
      aesop
    rw [he]
    by_cases ha : mrtPrimeAvoids (P j) n <;> by_cases ht : mrtTypical J P n <;>
      simp [mrtPrimeMask, ha, ht]

/-- Exact inclusion-exclusion over missing prime bands, the expansion in
MRT Appendix A before its near-twist mean-value estimate. -/
theorem mrtTypical_inclusion_exclusion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (n : ℕ) :
    (∑ I ∈ J.powerset, (-1 : ℝ) ^ I.card * mrtPrimeMask (I.biUnion P) n) =
      if mrtTypical J P n then 1 else 0 := by
  rw [← mrtTypical_prod, prod_sub]
  apply sum_congr rfl
  intro I _
  rw [prod_const_one, mul_one, mrtPrimeMask_biUnion]


/-- Dividing out a number smaller than all the selected primes does not
change membership in the typical-factorization set. -/
theorem mrtTypical_mul_of_avoids {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime) {d : ℕ}
    (hd : mrtPrimeAvoids (J.biUnion P) d) (n : ℕ) :
    mrtTypical J P (d * n) ↔ mrtTypical J P n := by
  constructor
  · intro h j hj
    obtain ⟨p, hp, hpdn⟩ := h j hj
    refine ⟨p, hp, ?_⟩
    exact ((hP j hj p hp).dvd_mul.mp hpdn).resolve_left
      (hd p (mem_biUnion.mpr ⟨j, hj, hp⟩))
  · intro h j hj
    obtain ⟨p, hp, hpn⟩ := h j hj
    exact ⟨p, hp, dvd_mul_of_dvd_right hpn d⟩



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalRamare
namespace OAI

/-! Ramaré factorization on the actual typical-factorization set.  Removing
one selected prime band leaves exactly the remaining-band condition; the
prime-square correction and its bound are retained. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators






lemma mrt_LSeries_term_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  rw [LSeries.term_of_ne_zero (Nat.mul_pos hm hn).ne', LSeries.term_of_ne_zero hm.ne',
    LSeries.term_of_ne_zero hn.ne', hF m n hm hn, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, div_mul_div_comm]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothEuler
namespace OAI

/-! The finite-prime smooth Euler product on Re(s)=1.  Finite prime
support makes the series absolutely convergent even on this line; the
geometric local factors therefore give the actual analytic series to
which the pretentious-distance estimate applies. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_line_one_euler_term (F : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term F (1 + (t : ℂ) * Complex.I) n = mrtPrimeEulerTerm F t n := by
  have he : conj (mrtArchimedeanTwist t n) =
      Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
    rw [mrtArchimedeanTwist, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [mrt_line_one_term F hn t, mrtPrimeEulerTerm, he]
  ring

lemma mrt_LSeries_term_pow (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    LSeries.term F s (p ^ k) = (LSeries.term F s p) ^ k := by
  induction k with
  | zero => simp [LSeries.term, hF1]
  | succ k ih =>
    calc
      _ = LSeries.term F s (p ^ k * p) := by rw [pow_succ]
      _ = LSeries.term F s (p ^ k) * LSeries.term F s p :=
        mrt_LSeries_term_mul F hF s (pow_pos hp k) hp
      _ = _ := by rw [ih, pow_succ]

lemma mrt_LSeries_term_coprime_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (_h : m.Coprime n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  exact mrt_LSeries_term_mul F hF s (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

lemma mrt_prime_euler_norm_lt_one (F : ℕ → ℂ) (hF : OneBounded F)
    (t : ℝ) {p : ℕ} (hp : p.Prime) : ‖mrtPrimeEulerTerm F t p‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (1 : ℝ) / p := mrtPrimeEulerTerm_norm_le F t hp.pos (hF p hp.pos)
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    _ < 1 := by norm_num

/-- The actual smooth L-series is absolutely summable and equals its
finite Euler product on the boundary line `Re(s)=1`. -/
theorem mrt_smooth_euler_product (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) :
    Summable (fun n : Nat.smoothNumbers (N + 1) =>
      ‖LSeries.term F (1 + (t : ℂ) * Complex.I) n‖) ∧
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      LSeries.term F (1 + (t : ℂ) * Complex.I) n)
      (∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have h1 : LSeries.term F s 1 = 1 := by simp [LSeries.term, hF1]
  have hlocal (p : ℕ) (hp : p.Prime) (k : ℕ) :
      LSeries.term F s (p ^ k) = (mrtPrimeEulerTerm F t p) ^ k := by
    rw [mrt_LSeries_term_pow F hF1 hF s hp.pos k,
      mrt_line_one_euler_term F hp.ne_zero t]
  have hnorm : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖LSeries.term F s (p ^ k)‖) := by
    intro p hp
    simpa only [hlocal p hp, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg _)
        (mrt_prime_euler_norm_lt_one F hFb t hp))
  obtain ⟨hs, he⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 (fun {_ _} h => mrt_LSeries_term_coprime_mul F hF s h) hnorm (N + 1)
  have hprod : (∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, LSeries.term F s (p ^ k)) =
      ∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹ := by
    change (∏ p ∈ primesUpTo N, ∑' k : ℕ, LSeries.term F s (p ^ k)) = _
    apply prod_congr rfl
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ = ∑' k : ℕ, (mrtPrimeEulerTerm F t p) ^ k := tsum_congr (hlocal p hprime)
      _ = _ := (hasSum_geometric_of_norm_lt_one
        (mrt_prime_euler_norm_lt_one F hFb t hprime)).tsum_eq
  rw [hprod] at he
  exact ⟨hs, he⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothTypical
namespace OAI

/-! The actual smooth Dirichlet series restricted to the typical set.
Finite inclusion-exclusion and the proved smooth Euler formula give the
exact product of nonempty-band Euler factors. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical


lemma mrtMaskedCoefficient_one (F : ℕ → ℂ) (hF : F 1 = 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : mrtMaskedCoefficient F P 1 = 1 := by
  simp only [mrtMaskedCoefficient, hF, mrtPrimeMask_one P hP, Complex.ofReal_one, mul_one]

lemma mrtMaskedCoefficient_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    mrtMaskedCoefficient F P (m * n) =
      mrtMaskedCoefficient F P m * mrtMaskedCoefficient F P n := by
  simp only [mrtMaskedCoefficient, hF m n hm hn, mrtPrimeMask_mul P hP,
    Complex.ofReal_mul]
  ring

lemma mrtMaskedCoefficient_oneBounded (F : ℕ → ℂ) (hF : OneBounded F)
    (P : Finset ℕ) : OneBounded (mrtMaskedCoefficient F P) := by
  intro n hn
  by_cases h : mrtPrimeAvoids P n
  · simpa [mrtMaskedCoefficient, mrtPrimeMask, h] using hF n hn
  · simp [mrtMaskedCoefficient, mrtPrimeMask, h]

lemma mrtMaskedCoefficient_term (F : ℕ → ℂ) (P : Finset ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (mrtMaskedCoefficient F P) s n =
      (mrtPrimeMask P n : ℂ) * LSeries.term F s n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, mrtMaskedCoefficient]
  ring

theorem mrt_masked_smooth_euler (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) (t : ℝ) :
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      LSeries.term (mrtMaskedCoefficient F P) (1 + (t : ℂ) * Complex.I) n)
      (∏ p ∈ primesUpTo N \ P, (1 - mrtPrimeEulerTerm F t p)⁻¹) := by
  have hs := (mrt_smooth_euler_product (mrtMaskedCoefficient F P)
    (mrtMaskedCoefficient_one F hF1 P hP) (mrtMaskedCoefficient_mul F hF P hP)
    (mrtMaskedCoefficient_oneBounded F hFb P) N t).2
  have he : (∏ p ∈ primesUpTo N,
      (1 - mrtPrimeEulerTerm (mrtMaskedCoefficient F P) t p)⁻¹) =
      ∏ p ∈ primesUpTo N \ P, (1 - mrtPrimeEulerTerm F t p)⁻¹ := by
    have hset : primesUpTo N \ P = (primesUpTo N).filter (fun p => p ∉ P) := by
      ext p
      simp
    rw [hset, prod_filter]
    apply prod_congr rfl
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    by_cases hpP : p ∈ P <;>
      simp [mrtPrimeEulerTerm, mrtMaskedCoefficient, mrtPrimeMask_prime P hP hprime, hpP]
  rwa [he] at hs

/-- Exact equation (A.11) before taking norms: the typical smooth series
equals a complement Euler product times the nonempty-band factors. -/
theorem mrt_typical_smooth_euler {ι : Type*} (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, P j ⊆ primesUpTo N) (hdis : Set.PairwiseDisjoint (J : Set ι) P) :
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      if mrtTypical J P n then LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0)
      ((∏ p ∈ primesUpTo N \ J.biUnion P, (1 - mrtPrimeEulerTerm F t p)⁻¹) *
        ∏ j ∈ J, ((∏ p ∈ P j, (1 - mrtPrimeEulerTerm F t p)⁻¹) - 1)) := by
  have hprime (I : Finset ι) (hI : I ∈ J.powerset) :
      ∀ p ∈ I.biUnion P, p.Prime := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp
    exact (mem_filter.mp (hP j (mem_powerset.mp hI hj) hpj)).2
  have hs := hasSum_sum (s := J.powerset) (fun I hI =>
    (mrt_masked_smooth_euler F hF1 hF hFb (I.biUnion P) (hprime I hI) N t).mul_left
      ((-1 : ℂ) ^ I.card))
  have hpoint (n : Nat.smoothNumbers (N + 1)) :
      (∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        LSeries.term (mrtMaskedCoefficient F (I.biUnion P))
          (1 + (t : ℂ) * Complex.I) n) =
      if mrtTypical J P n then LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0 := by
    have hi : (∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        (mrtPrimeMask (I.biUnion P) n : ℂ)) = if mrtTypical J P n then 1 else 0 := by
      have hh := congrArg Complex.ofRealHom (mrtTypical_inclusion_exclusion J P (n : ℕ))
      simpa only [map_sum, map_mul, map_pow, map_neg, map_one, apply_ite, map_zero,
        Complex.ofRealHom_eq_coe] using hh
    simp only [mrtMaskedCoefficient_term, ← mul_assoc, ← sum_mul, hi]
    split_ifs <;> simp
  have hfun : (fun n : Nat.smoothNumbers (N + 1) =>
      ∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        LSeries.term (mrtMaskedCoefficient F (I.biUnion P))
          (1 + (t : ℂ) * Complex.I) n) =
      (fun n : Nat.smoothNumbers (N + 1) => if mrtTypical J P n then
        LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0) := funext hpoint
  rw [hfun] at hs
  convert (preTransparency := .instances) hs using 1
  exact (mrt_euler_inclusion_exclusion (primesUpTo N) J P
    (fun p => (1 - mrtPrimeEulerTerm F t p)⁻¹) hP hdis).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrtTypicalCoefficient_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) :
    OneBounded (mrtTypicalCoefficient J P F) := by
  intro n hn
  unfold mrtTypicalCoefficient
  split_ifs
  · exact hF n hn
  · simp





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalOutside
namespace OAI

/-! Multiplication outside the selected prime bands preserves the typical
mask. The resulting identity uses the unmasked factor on the left: the
typical coefficient itself need not be multiplicative. In particular, the
complete part can be extracted at every power of an outside prime, without
a coprimality condition on the remaining argument. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrtPrimeAvoids_prime_outside (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) {p : ℕ} (hp : p.Prime) (hpout : p ∉ P) :
    mrtPrimeAvoids P p := by
  intro q hq hqp
  have he : q = p := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp
  exact hpout (he ▸ hq)


/-- Extract an avoiding factor from a completely multiplicative coefficient,
while keeping the same typical mask on the cofactor. -/
theorem mrtTypicalCoefficient_mul_of_avoids {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (havoid : mrtPrimeAvoids (J.biUnion P) d) :
    mrtTypicalCoefficient J P F (d * n) = F d * mrtTypicalCoefficient J P F n := by
  unfold mrtTypicalCoefficient
  rw [mrtTypical_mul_of_avoids J P hP havoid n]
  split_ifs
  · exact hF d n hd hn
  · simp only [mul_zero]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothSeries
namespace OAI

/-! The smooth Euler series used in the triple-convolution Perron formula.
The finite prime factors and the smooth factor are absolutely convergent
on the line Re(s)=1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike DeltaSpikeContinuous Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.Classical _root_.LSeries.notation



lemma halasz_smooth_term (f : ℕ → ℂ) (N : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (halaszSmoothFunction f N) s n =
      (Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s) n := by
  by_cases hn : n ∈ Nat.smoothNumbers (N + 1) <;>
    simp [LSeries.term, halaszSmoothFunction, hn]

lemma halasz_smooth_LSeries (f : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeries (halaszSmoothFunction f N) s =
      ∑' n : Nat.smoothNumbers (N + 1), LSeries.term f s n := by
  rw [LSeries, _root_.tsum_subtype (Nat.smoothNumbers (N + 1)) (LSeries.term f s)]
  exact tsum_congr (halasz_smooth_term f N s)







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]



theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring







theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]


lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩





lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top


private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp





section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end











theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply Real.log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind



theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply Real.log_pos; norm_num
        linarith [E₁.nonneg]




























end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
namespace OAI

/-! Mertens' second theorem in bounded-error form.

The formal proof uses `Erdos970.Mertens.sum_prime_div_eq_log_log`.
Only the convention for the finite prime set differs from
`PrimeReciprocalInput`; zero contributes no prime to either convention.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma sievePrimesUpTo_eq_Ioc (x : ℝ) :
    sievePrimesUpTo x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [sievePrimesUpTo, mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hp, hprime⟩

/-- Mertens' second theorem implies the reciprocal-prime estimate. -/
theorem primeReciprocalInput : PrimeReciprocalInput := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx => ?_⟩
  rw [sievePrimesUpTo_eq_Ioc]
  exact hC x hx

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass
namespace OAI

/-! Mertens' first theorem, in the prime-band convention needed for the
small- and large-prime truncations in the Halasz convolution. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszMertensConstant_nonneg : 0 ≤ halaszMertensConstant := by
  unfold halaszMertensConstant
  positivity







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszParameters
namespace OAI

/-! The logarithmic truncation height and integer smoothing length used
in the grouped Perron estimate. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma halasz_eventually_numeric_scale (B : ℝ) :
    ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 1 ≤ Real.log (Real.log x) ∧
      2 ≤ Real.log x ^ 4 ∧ Real.log x ^ 16 ≤ x / 2 ∧ B ≤ Real.log x ^ 8 := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 16)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 B))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_ge_atTop (3 : ℝ), hlog, hloglog, hsmall] with x hx hl hll hs
  have hl2 : 2 ≤ Real.log x := (le_max_left _ _).trans hl
  have hl1 : 1 ≤ Real.log x := by linarith
  dsimp only [id] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log x) 16),
    Real.norm_eq_abs, abs_of_pos (by linarith : 0 < x)] at hs
  refine ⟨hx, hll, ?_, by linarith, ?_⟩
  · exact hl2.trans (le_self_pow₀ hl1 (by norm_num : (4 : ℕ) ≠ 0))
  · exact ((le_max_right _ _).trans hl).trans (le_self_pow₀ hl1 (by norm_num : (8 : ℕ) ≠ 0))

lemma halasz_smoothing_integer {N : ℕ} (hN : 2 ≤ N)
    (hlog : 2 ≤ Real.log (N : ℝ) ^ 4) (hsmall : Real.log (N : ℝ) ^ 4 ≤ N) :
    let m := ⌈(N : ℝ) / Real.log (N : ℝ) ^ 4⌉₊
    0 < m ∧ m ≤ N ∧ (N : ℝ) / Real.log (N : ℝ) ^ 4 ≤ m ∧
      (m : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ) ^ 4) ∧
      ((N : ℝ) + 1 / 2) / m ≤ 2 * Real.log (N : ℝ) ^ 4 := by
  let L := Real.log (N : ℝ) ^ 4
  let m := ⌈(N : ℝ) / L⌉₊
  have hL : 0 < L := by dsimp [L]; linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hratio : 1 ≤ (N : ℝ) / L := (le_div_iff₀ hL).mpr (by simpa [L] using hsmall)
  have hratioHigh : (N : ℝ) / L ≤ (N : ℝ) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
  have hmlo : (N : ℝ) / L ≤ m := Nat.le_ceil _
  have hmhi : (m : ℝ) < (N : ℝ) / L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmp : (0 : ℝ) < m := by linarith
  have hmNat : 0 < m := by exact_mod_cast hmp
  have hmN : m ≤ N := by exact_mod_cast (show (m : ℝ) ≤ N by linarith)
  refine ⟨hmNat, hmN, hmlo, by linarith, ?_⟩
  apply (div_le_iff₀ hmp).mpr
  have hmul : (N : ℝ) ≤ (m : ℝ) * L := (div_le_iff₀ hL).mp hmlo
  dsimp [L] at hmul ⊢
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNumericalErrors
namespace OAI

/-! The logarithmic height and integer smoothing length absorb the two
errors in the grouped Perron estimate. -/

namespace TwoPointCorrelations

lemma halasz_numerical_errors {N m : ℕ} {C H : ℝ}
    (hN : 3 ≤ N) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hm : 0 < m)
    (hml : (m : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ) ^ 4))
    (hmu : ((N : ℝ) + 1 / 2) / m ≤ 2 * Real.log (N : ℝ) ^ 4) :
    C * N * (H * Real.log N) * Real.log N /
        (((m : ℝ) / ((N : ℝ) + 1 / 2)) * Real.log N ^ 8) +
      C * m * Real.log (3 * N) ^ 2 ≤ (2 * C * H + 8 * C) * N := by
  let ℓ := Real.log (N : ℝ)
  have hℓ : 1 ≤ ℓ := hlog
  have hℓ0 : 0 < ℓ := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) ≤ 2 * ℓ ^ 8 := by
    calc
      _ ≤ ℓ ^ 2 * (2 * ℓ ^ 4) := mul_le_mul_of_nonneg_left hmu (sq_nonneg _)
      _ = 2 * ℓ ^ 6 := by ring
      _ ≤ 2 * ℓ ^ 8 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hℓ (by norm_num : (6 : ℕ) ≤ 8)) (by norm_num)
  have hfacdiv : ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) / ℓ ^ 8 ≤ 2 :=
    (div_le_iff₀ (pow_pos hℓ0 8)).mpr hfac
  have htail : C * N * (H * ℓ) * ℓ /
      (((m : ℝ) / ((N : ℝ) + 1 / 2)) * ℓ ^ 8) ≤ 2 * C * H * N := by
    calc
      _ = (C * N * H) * (ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) / ℓ ^ 8) := by
        field_simp
      _ ≤ (C * N * H) * 2 := mul_le_mul_of_nonneg_left hfacdiv (by positivity)
      _ = _ := by ring
  have hlog3 : 0 ≤ Real.log (3 * (N : ℝ)) := by
    apply Real.log_nonneg
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog3u : Real.log (3 * (N : ℝ)) ≤ 2 * ℓ := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have : Real.log 3 ≤ ℓ := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    linarith
  have hboundary : C * m * Real.log (3 * (N : ℝ)) ^ 2 ≤ 8 * C * N := by
    calc
      _ ≤ C * (2 * ((N : ℝ) / ℓ ^ 4)) * (2 * ℓ) ^ 2 := by gcongr
      _ = 8 * C * N / ℓ ^ 2 := by field_simp; ring
      _ ≤ 8 * C * N := div_le_self (by positivity) (one_le_pow₀ hℓ)
  change C * N * (H * ℓ) * ℓ /
      (((m : ℝ) / ((N : ℝ) + 1 / 2)) * ℓ ^ 8) +
      C * m * Real.log (3 * (N : ℝ)) ^ 2 ≤ _
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedNumeric
namespace OAI

/-! The cost of deleting primes below the upper endpoint of the typical
bands, before applying the mixed Perron estimate. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma halaszMixedNumericConstant_nonneg : 0 ≤ halaszMixedNumericConstant := by
  have := halaszPrimePowerConstant_nonneg
  have := halaszMertensConstant_nonneg
  have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold halaszMixedNumericConstant
  positivity


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothDistance
namespace OAI

/-! Mertens turns the exact smooth Euler product into the usual
`log N * exp(-distance)` estimate, uniformly in the bounded coefficient. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_sievePrimesUpTo_nat (N : ℕ) : sievePrimesUpTo (N : ℝ) = primesUpTo N := by
  ext p
  simp only [sievePrimesUpTo, primesUpTo, mem_filter, mem_Iic, Nat.floor_natCast,
    mem_range, Nat.lt_succ_iff]

lemma mrt_prime_inverse_square_sum (N : ℕ) :
    (∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  have hs : primesUpTo N ⊆ Ioo 0 (N + 1) := by
    intro p hp
    exact mem_Ioo.mpr ⟨(mem_filter.mp hp).2.pos, mem_range.mp (mem_filter.mp hp).1⟩
  calc
    _ ≤ ∑ n ∈ Ioo 0 (N + 1), ((n : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ ≤ 2 := by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothBounds
namespace OAI

/-! Continuity and uniform bounds for the actual smooth Euler series on
the Perron line. Only values at positive integers are bounded. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

lemma halasz_distance_nonneg (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) (t : ℝ) :
    0 ≤ squaredDistance f (mrtArchimedeanTwist t) N := by
  unfold squaredDistance
  apply sum_nonneg
  intro p hp
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hprime : p.Prime := (mem_filter.mp hp).2
  have hn : ‖f p * star (mrtArchimedeanTwist t p)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, mrtArchimedeanTwist_norm, mul_one] using hf p hprime.pos
  exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hn)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalEulerBound
namespace OAI

/-! The exact typical smooth Euler product retains half of the full
pretentious-distance exponent, independently of the number of bands. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.Classical

theorem mrt_typical_smooth_euler_bound {ι : Type*} (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, P j ⊆ primesUpTo N) (hdis : Set.PairwiseDisjoint (J : Set ι) P) :
    ‖∑' n : Nat.smoothNumbers (N + 1),
      if mrtTypical J P n then LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N / 2 +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  let z : ℕ → ℂ := mrtPrimeEulerTerm F t
  have hz (p : ℕ) (hp : p ∈ primesUpTo N) : ‖z p‖ ≤ 1 / 2 := by
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    exact (mrtPrimeEulerTerm_norm_le F t hprime.pos (hFb p hprime.pos)).trans
      (one_div_le_one_div_of_le (by norm_num) hp2)
  rw [(mrt_typical_smooth_euler F hF1 hF hFb N t J P hP hdis).tsum_eq]
  have he := mrt_partitioned_euler_bound (primesUpTo N) J P z hP hdis hz
  apply he.trans
  have hmass : (∑ p ∈ primesUpTo N, (‖z p‖ + ‖z p‖ ^ 2)) ≤
      (∑ p ∈ primesUpTo N, (1 : ℝ) / p) +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hn := mrtPrimeEulerTerm_norm_le F t hprime.pos (hFb p hprime.pos)
    apply add_le_add hn
    simpa only [one_div, inv_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hfull := mrt_finite_euler_distance_bound F hFb t N
  calc
    _ ≤ Real.sqrt (Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
          squaredDistance F (mrtArchimedeanTwist t) N +
          ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2)) *
        Real.exp (((∑ p ∈ primesUpTo N, (1 : ℝ) / p) +
          ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) / 2) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hfull)
        (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hmass (by norm_num)))
        (Real.exp_pos _).le (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.exp_half, ← Real.exp_add]
      congr 1
      ring

/-- The absolute constant does not depend on the number or positions of
the disjoint prime bands. -/
theorem mrt_typical_smooth_distance_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (F : ℕ → ℂ), F 1 = 1 →
      (∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n) → OneBounded F →
      ∀ (N : ℕ), 2 ≤ N → ∀ (t : ℝ) {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, P j ⊆ primesUpTo N) → Set.PairwiseDisjoint (J : Set ι) P →
      ‖∑' n : Nat.smoothNumbers (N + 1),
        if mrtTypical J P n then LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0‖ ≤
        C * Real.log N * Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N / 2) := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  refine ⟨Real.exp (C + 2), Real.exp_pos _, ?_⟩
  intro F hF1 hF hFb N hN t ι J P hP hdis
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hm := hC (N : ℝ) hN2
  rw [mrt_sievePrimesUpTo_nat] at hm
  have hmass := (abs_le.mp hm).2
  have hsq := mrt_prime_inverse_square_sum N
  calc
    _ ≤ Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N / 2 +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) :=
      mrt_typical_smooth_euler_bound F hF1 hF hFb N t J P hP hdis
    _ ≤ Real.exp (C + 2 + Real.log (Real.log N) +
        (-squaredDistance F (mrtArchimedeanTwist t) N / 2)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hlog]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalSmooth
namespace OAI

/-! The central Euler estimate for the literal typical coefficient on
the same smooth series used by the mixed convolution. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_typical_smooth_series {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeries (halaszSmoothFunction (mrtTypicalCoefficient J P F) N) s =
      ∑' n : Nat.smoothNumbers (N+1), if mrtTypical J P n then LSeries.term F s n else 0 := by
  rw [halasz_smooth_LSeries]
  apply tsum_congr
  intro n
  by_cases hn : mrtTypical J P n
  · simp [LSeries.term,mrtTypicalCoefficient,hn]
  · simp [LSeries.term,mrtTypicalCoefficient,hn]

theorem halasz_typical_smooth_distance_bound : ∃ C : ℝ, 0 < C ∧
    ∀ F : ℕ → ℂ, F 1=1 →
      (∀ m n, 0 < m → 0 < n → F (m*n)=F m*F n) → OneBounded F →
      ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, P j ⊆ primesUpTo N) → Set.PairwiseDisjoint (J : Set ι) P →
      ‖LSeries (halaszSmoothFunction (mrtTypicalCoefficient J P F) N)
        (1+(t:ℂ)*Complex.I)‖ ≤
        C*Real.log N*Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N/2) := by
  obtain ⟨C,hC,hbound⟩ := mrt_typical_smooth_distance_bound
  refine ⟨C,hC,?_⟩
  intro F hF1 hF hFb N hN t ι J P hP hdis
  rw [halasz_typical_smooth_series]
  exact hbound F hF1 hF hFb N hN t J P hP hdis

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalMean
namespace OAI

/-! Ordinary prefixes of the literal typical coefficient. The prime
cutoff stays above all selected bands throughout both convolutions. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem halasz_typical_mean_value_oai : ∃ C X₀ : ℝ, 0  <  C ∧
    ∀ N : ℕ, X₀  ≤  N → ∀ F : ℕ → ℂ, F 1=1 →
      (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, P j  ⊆  primesUpTo N) → Set.PairwiseDisjoint (J : Set ι) P →
      ∀ R : ℝ, 1 ≤ R → Real.log (N:ℝ)^16 ≤ R → R ≤ (N:ℝ)/2 →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ R) → ∀ M : ℝ, 0 ≤ M →
      (∀ t ∈ Set.Icc (-(Real.log (N:ℝ)^8)) (Real.log (N:ℝ)^8),
        M ≤ squaredDistance F (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, mrtTypicalCoefficient J P F n‖  ≤  C*N*
        ((M+1)*Real.exp (-M/2)+(1+Real.log R)*Real.log (Real.log N)/Real.log N) := by
  obtain ⟨C₁,T₀,hC₁,hT₀,hdouble⟩ := halasz_mixed_double_estimate
  obtain ⟨H₀,hH₀,hEuler⟩ := halasz_typical_smooth_distance_bound
  let H := max 1 H₀
  let D := 2*C₁*H+8*C₁+halaszMixedNumericConstant
  let C := 1+C₁*H+D
  have hH : 1 ≤ H := le_max_left _ _
  have hH₀H : H₀ ≤ H := le_max_right _ _
  have hD : 0 ≤ D := by
    dsimp [D]
    have := halaszMixedNumericConstant_nonneg
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp ((halasz_eventually_numeric_scale T₀).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))))
  refine ⟨C,X₀,hC,?_⟩
  intro N hXN F hF1 hFm hFb ι J P hP hdis R hR hRlo hRhi hupper M hM hdist
  obtain ⟨⟨hNr,hll,hl4,hl16,hBT⟩,hlog⟩ := hX₀ N hXN
  have hN : 3 ≤ N := by exact_mod_cast hNr
  have hN2 : 2 ≤ N := by omega
  have hlog0 : 0 < Real.log (N:ℝ) := by linarith
  have hl4N : Real.log (N:ℝ)^4 ≤ N :=
    (pow_le_pow_right₀ hlog (by norm_num : (4:ℕ) ≤ 16)).trans (by linarith)
  let B := mrtTypicalCoefficient J P F
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded J P F hFb
  have hpr : ∀ j ∈ J, ∀ p ∈ P j, p.Prime := by
    intro j hj p hp
    exact (mem_filter.mp (hP j hj hp)).2
  have hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=F p*B m := by
    intro p hp hRp m hm
    have ha : mrtPrimeAvoids (J.biUnion P) p := by
      apply mrtPrimeAvoids_prime_outside _ (fun q hq => ?_) hp
      · intro hmem
        obtain ⟨j,hj,hpj⟩ := mem_biUnion.mp hmem
        exact (not_le_of_gt hRp) (hupper j hj p hpj)
      · obtain ⟨j,hj,hqj⟩ := mem_biUnion.mp hq
        exact hpr j hj q hqj
    exact mrtTypicalCoefficient_mul_of_avoids J P hpr F hFm hp.pos hm ha
  let m := ⌈(N:ℝ)/Real.log (N:ℝ)^4⌉₊
  obtain ⟨hm,hmN,_,hml,hmu⟩ := halasz_smoothing_integer hN2 hl4 hl4N
  have hglobal (t : ℝ) : ‖LSeries (halaszSmoothFunction B N) (1+(t:ℂ)*Complex.I)‖  ≤
      H*Real.log N := by
    have he := hEuler F hF1 hFm hFb N hN2 t J P hP hdis
    have hd := halasz_distance_nonneg F hFb N t
    have hx : Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N/2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      _  ≤  H₀*Real.log N*Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N/2) := he
      _  ≤  H₀*Real.log N := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ H₀*Real.log (N:ℝ))
      _  ≤  _ := mul_le_mul_of_nonneg_right hH₀H hlog0.le
  have hcentral (t : ℝ) (ht : t ∈ Set.Icc (-(Real.log (N:ℝ)^8)) (Real.log (N:ℝ)^8)) :
      ‖LSeries (halaszSmoothFunction B N) (1+(t:ℂ)*Complex.I)‖  ≤
        (H*Real.log N)*Real.exp (-(M/2)) := by
    apply (hEuler F hF1 hFm hFb N hN2 t J P hP hdis).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hH₀H hlog0.le
    · apply Real.exp_le_exp.mpr
      linarith [hdist t ht]
    · positivity
    · positivity
  have hb := hdouble F B hFb hB N m R (Real.log N^8) (H*Real.log N)
    (H*Real.log N) (M/2) hN2 hm hmN hR
    (by rw [←pow_mul]; norm_num; exact hRlo) hBT
    (le_mul_of_one_le_left hlog0.le hH) (by positivity) (by positivity) hcentral hglobal
  have herr := halasz_numerical_errors hN hC₁.le (by linarith : 0 ≤ H) hlog hm hml hmu
  have hr := Real.log_nonneg hR
  have hreduce := halasz_mixed_mean_numeric F B hFb hB N hR hRhi hll hmul
  have hsmall : (2*C₁*H+8*C₁)*N  ≤
      (2*C₁*H+8*C₁)*N*(1+Real.log R)*Real.log (Real.log N) := by
    calc
      _ ≤ (2*C₁*H+8*C₁)*N*(1+Real.log R) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hll
  have hmain : Real.log (N:ℝ)*‖∑ n ∈ Icc 1 N, B n‖  ≤
      C₁*N*(H*Real.log N)*(M+1)*Real.exp (-M/2)+
        D*N*(1+Real.log R)*Real.log (Real.log N) := by
    have hmfac : C₁*N*(H*Real.log N)*(M/2+1)*Real.exp (-(M/2))  ≤
        C₁*N*(H*Real.log N)*(M+1)*Real.exp (-M/2) := by
      rw [show -(M/2) = -M/2 by ring]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    dsimp [D]
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hmain hlog0.le
  have heq : (C₁*N*(H*Real.log N)*(M+1)*Real.exp (-M/2)+
      D*N*(1+Real.log R)*Real.log (Real.log N))/Real.log N =
      C₁*H*N*((M+1)*Real.exp (-M/2))+
        D*N*((1+Real.log R)*Real.log (Real.log N)/Real.log N) := by field_simp
  rw [mul_div_cancel_left₀ _ hlog0.ne',heq] at hdiv
  have hc1 : C₁*H ≤ C := by dsimp [C]; linarith
  have hc2 : D ≤ C := by dsimp [C]; linarith [show 0 ≤ C₁*H by positivity]
  calc
    _  ≤  C₁*H*N*((M+1)*Real.exp (-M/2))+
        D*N*((1+Real.log R)*Real.log (Real.log N)/Real.log N) := hdiv
    _  ≤  C*N*((M+1)*Real.exp (-M/2))+
        C*N*((1+Real.log R)*Real.log (Real.log N)/Real.log N) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_typical_mean_value_oai := @OAI.TwoPointCorrelations.halasz_typical_mean_value_oai
