-- Prove2me | solution 1 for OAI.JointDickman.amplification_positive_mass_bound_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:04:20.210975+00:00
-- url     : https://prove2.me/submissions/f6e71b66-a9ca-45a4-b116-5c6cbb539960

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_bounded_box_coarse_comparison_jd
import Theorems.Thm_OAI_JointDickman_weighted_geometric_period_model_vanishing_jd

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OscillatoryTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth oscillatory tests used in the coefficient estimate -/

namespace JointDickman

theorem hasDerivAt_additivePhase (x : ℝ) :
    HasDerivAt additivePhase (additivePhase x * ((2 * Real.pi : ℝ) * Complex.I)) x := by
  have h := (((hasDerivAt_id x).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simpa only [mul_one, id_eq] using! h

theorem continuous_additivePhase : Continuous additivePhase :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_additivePhase x).continuousAt)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditivePhaseBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relating real exponential notation to residue characters -/

namespace JointDickman

theorem additivePhase_add (s t : ℝ) :
    additivePhase (s + t) = additivePhase s * additivePhase t := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSetWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prime-selection and fair-split weights

The independent prime-set model and its fair splits satisfy exact finite
identities without prime asymptotics or analytic equidistribution premises.
-/

namespace JointDickman

open scoped BigOperators

theorem bernoulliSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    0 ≤ bernoulliSubsetMass P q S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p hp => (hq p (hS hp)).1)
  · exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hq p
      (Finset.mem_sdiff.mp hp).1).2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing finite product laws

Replacing one independent coordinate at a time bounds the `L¹` distance
of two finite product probability laws by the sum of their coordinate
distances. Applied to the mutually exclusive prime-site law, this gives
the accumulated quadratic error for arbitrary bounded complex tests.
All identities and inequalities here are proved by finite sums.
-/

namespace JointDickman

open scoped BigOperators

theorem finiteProductMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    (a : ∀ i, Ω i → ℝ) (ha : ∀ i x, 0 ≤ a i x) (x : ∀ i, Ω i) :
    0 ≤ finiteProductMass a x :=
  Finset.prod_nonneg (fun i _ => ha i (x i))

theorem finiteProductMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (a : ∀ i, Ω i → ℝ)
    (ha : ∀ i, ∑ x, a i x = 1) : ∑ x, finiteProductMass a x = 1 := by
  classical
  unfold finiteProductMass
  rw [← Fintype.prod_sum]
  simp only [ha, Finset.prod_const_one]

theorem bernoulliBitMass_sum (q : ℝ) : ∑ b, bernoulliBitMass q b = 1 := by
  simp [bernoulliBitMass]

theorem bernoulliBitMass_nonneg {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) (b : Bool) :
    0 ≤ bernoulliBitMass q b := by
  cases b <;> simp only [bernoulliBitMass, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr hq.2
  · exact hq.1

theorem bernoulliSubsetMass_eq_product {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : P.powerset) :
    finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val)) (subsetHitEquiv P S) =
      bernoulliSubsetMass P q S.val := by
  classical
  have hp : finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val))
      (subsetHitEquiv P S) = ∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val := by
    unfold finiteProductMass
    apply Finset.prod_congr rfl
    intro i _
    simp [bernoulliBitMass, subsetHitEquiv]
  rw [hp, show (∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val) =
    ∏ i ∈ P, if i ∈ S.val then q i else 1 - q i from
      Finset.prod_coe_sort P (fun i => if i ∈ S.val then q i else 1 - q i), Finset.prod_ite]
  have hs : P.filter (fun i => i ∈ S.val) = S.val := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => Finset.mem_powerset.mp S.property hi)
  have hc : P.filter (fun i => i ∉ S.val) = P \ S.val := by
    ext i
    simp
  rw [hs, hc]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReciprocalTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative reciprocal-square tails

The error in the independent-product replacement is controlled by the tail
of all integers; no prime number theorem is needed here.
-/

namespace JointDickman

open Finset

theorem sum_reciprocal_square_tail (Q : Finset ℕ) {N : ℕ} (hN : N ≠ 0)
    (hQ : ∀ q ∈ Q, N < q) : (∑ q ∈ Q, 1 / (q : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let M := max N (Q.sup id)
  have hsub : Q ⊆ Ioc N M := by
    intro q hq
    exact mem_Ioc.mpr ⟨hQ q hq, (le_sup (f := id) hq).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑ q ∈ Ioc N M, 1 / (q : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
      simpa only [one_div] using (sum_Ioc_inv_sq_le_sub (α := ℝ) hN (le_max_left _ _))
    _ ≤ _ := sub_le_self _ (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogProductBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite logarithmic errors for prime-product normalizations

The quadratic logarithmic error is summable above the lower prime cutoff.
The inverse factors in the exact Bernoulli product mass are controlled
separately by a reciprocal sum over the selected primes.
-/

namespace JointDickman

open Finset

theorem log_one_sub_add_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hbase : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx, add_comm] using h
  have hden : 0 < 1 - x := by linarith
  apply hbase.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem finite_log_product_error {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    |Real.log (∏ i ∈ P, (1 - x i)) + ∑ i ∈ P, x i| ≤ 2 * ∑ i ∈ P, (x i) ^ 2 := by
  rw [Real.log_prod (fun i hi => by linarith [(hx i hi).2]), ← sum_add_distrib]
  calc
    _ ≤ ∑ i ∈ P, |Real.log (1 - x i) + x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, 2 * (x i) ^ 2 := sum_le_sum fun i hi =>
      log_one_sub_add_error (hx i hi).1 (hx i hi).2
    _ = _ := (mul_sum _ _ _).symm

/-- A selected-prime normalizer differs logarithmically from the linear
reciprocal-prime sum by at most the reciprocal-square tail. -/
theorem prime_log_product_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ P, N < p) :
    |Real.log (∏ p ∈ P, (1 - z / (p : ℝ))) + z * ∑ p ∈ P, 1 / (p : ℝ)| ≤
      2 * z ^ 2 / (N : ℝ) := by
  have hx (p : ℕ) (hp : p ∈ P) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have h := finite_log_product_error P (fun p => z / (p : ℝ)) hx
  have heq : (∑ p ∈ P, (z / (p : ℝ)) ^ 2) = z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    simp only [div_pow, mul_one_div]
  rw [heq] at h
  have hlin : (∑ p ∈ P, z / (p : ℝ)) = z * ∑ p ∈ P, 1 / (p : ℝ) := by
    simp only [mul_sum, mul_one_div]
  rw [hlin] at h
  calc
    _ ≤ 2 * (z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2) := h
    _ ≤ 2 * (z ^ 2 * (1 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (sq_nonneg z))
        (by norm_num)
    _ = _ := by ring

/-- The exact odds correction is bounded by an exponential of the
selected reciprocal mass, uniformly in the number of allowed primes. -/
theorem inverse_product_le_exp {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    (∏ i ∈ P, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ P, x i) := by
  have hpoint (i : ι) (hi : i ∈ P) : (1 - x i)⁻¹ ≤ Real.exp (2 * x i) := by
    have hpos : 0 < 1 - x i := by linarith [(hx i hi).2]
    have herr := log_one_sub_add_error (hx i hi).1 (hx i hi).2
    have hlog : Real.log ((1 - x i)⁻¹) ≤ 2 * x i := by
      rw [Real.log_inv]
      have hmul := mul_nonneg (hx i hi).1 (show 0 ≤ 1 - 2 * x i by linarith [(hx i hi).2])
      nlinarith [(abs_le.mp herr).1]
    calc
      _ = Real.exp (Real.log ((1 - x i)⁻¹)) := (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ ∏ i ∈ P, Real.exp (2 * x i) := Finset.prod_le_prod
      (fun i hi => inv_nonneg.mpr (by linarith [(hx i hi).2])) hpoint
    _ = Real.exp (∑ i ∈ P, 2 * x i) := (Real.exp_sum P (fun i => 2 * x i)).symm
    _ = _ := by rw [← mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact removal of the small prime factors

Removing a finite set of prime factors is an exact convolution identity.
The moving roughness cutoff is then controlled by Selberg–Delange estimates.
-/

namespace JointDickman

open ArithmeticFunction Finset

theorem smoothCorrection_isMultiplicative (E : Finset ℕ) (z : ℝ) :
    (smoothCorrection E z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨smoothCorrection_one E z, fun {m n} hm hn _ => ?_⟩
  simp only [smoothCorrection, coe_mk, hm, hn, mul_ne_zero hm hn,
    ↓reduceIte, Nat.primeFactors_mul hm hn, union_subset_iff,
    cardFactors_mul hm hn, pow_add, ite_zero_mul_ite_zero]

theorem smoothCorrection_prime_pow (E : Finset ℕ) (z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    smoothCorrection E z (p ^ k) = if p ∈ E then (-z) ^ k else 0 := by
  rw [smoothCorrection, coe_mk, ite_eq_right (pow_ne_zero k hp.ne_zero),
    Nat.primeFactors_pow p hk, hp.primeFactors]
  simp [cardFactors_apply_prime_pow hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal primes on fixed logarithmic intervals

Mertens' second theorem supplies the fixed-power interval limit. Together
with Chebyshev's estimate, it bounds the error in the marginal tuple count.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primesLE_eq_filter (N : ℕ) :
    Nat.primesLE N = (Icc 2 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.two_le, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

theorem largePrimeSet_eq_sdiff {N y : ℝ} (hy : 0 ≤ y) :
    largePrimeSet N y = Nat.primesLE ⌊N⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  apply Finset.ext
  intro p
  rw [Finset.mem_sdiff]
  simp only [largePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpy⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    rintro ⟨hpy', _⟩
    exact (not_le_of_gt hpy) ((Nat.le_floor_iff hy).mp hpy')
  · rintro ⟨⟨hpN, hp⟩, hnot⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    by_contra h
    exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩

theorem largePrimeSet_reciprocal_eq {N y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) :
    (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) = primeReciprocalSum N - primeReciprocalSum y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊N⌋₊ := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyN), hp⟩
  rw [largePrimeSet_eq_sdiff hy]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the independent prime-product law

The logarithm of the all-absent probability is its linear prime sum up to
a reciprocal-square error. Mertens' second theorem therefore determines
the normalization for a moving lower and upper cutoff.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Both endpoint Mertens remainders control the prime-interval remainder. -/
theorem prime_interval_mertens_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 2 ≤ X → X ≤ Y →
      |(∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) -
        (Real.log (Real.log Y) - Real.log (Real.log X))| ≤
        C / Real.log Y + C / Real.log X := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨C, hC, fun X Y hX hXY => ?_⟩
  have hY : 2 ≤ Y := hX.trans hXY
  have h₁ : |primeReciprocalSum X - Real.log (Real.log X) - M| ≤ C / Real.log X := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound X hX
  have h₂ : |primeReciprocalSum Y - Real.log (Real.log Y) - M| ≤ C / Real.log Y := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound Y hY
  rw [largePrimeSet_reciprocal_eq (by linarith) hXY]
  calc
    _ = |(primeReciprocalSum Y - Real.log (Real.log Y) - M) -
        (primeReciprocalSum X - Real.log (Real.log X) - M)| := by congr 1; ring
    _ ≤ |primeReciprocalSum Y - Real.log (Real.log Y) - M| +
        |primeReciprocalSum X - Real.log (Real.log X) - M| := abs_sub _ _
    _ ≤ _ := add_le_add h₂ h₁

/-- Uniform logarithmic normalizer error, retaining both endpoint errors. -/
theorem primeNormalizer_log_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (Y z : ℝ), 2 ≤ N → (N : ℝ) ≤ Y →
      0 ≤ z → z ≤ 1 →
      |Real.log (primeNormalizer (largePrimeSet Y N) z) +
        z * Real.log (Real.log Y / Real.log N)| ≤
        2 * z ^ 2 / (N : ℝ) + z * (C / Real.log Y + C / Real.log N) := by
  obtain ⟨C, hC, hinterval⟩ := prime_interval_mertens_error hM
  refine ⟨C, hC, fun N Y z hN hNY hz hz1 => ?_⟩
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hP : ∀ p ∈ largePrimeSet Y (N : ℝ), p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet Y (N : ℝ), N < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have h₁ := prime_log_product_error (largePrimeSet Y N) hP hz hz1
    (show N ≠ 0 by omega) hcut
  have h₂ := hinterval (N : ℝ) Y hNreal hNY
  have hlog : Real.log (Real.log Y / Real.log N) =
      Real.log (Real.log Y) - Real.log (Real.log N) :=
    Real.log_div hlogY.ne' hlogN.ne'
  let S := ∑ p ∈ largePrimeSet Y (N : ℝ), 1 / (p : ℝ)
  change |Real.log (primeNormalizer (largePrimeSet Y N) z) + z * Real.log (Real.log Y / Real.log N)| ≤ _
  calc
    _ = |(Real.log (primeNormalizer (largePrimeSet Y N) z) + z * S) +
        z * (Real.log (Real.log Y / Real.log N) - S)| := by congr 1; ring
    _ ≤ |Real.log (primeNormalizer (largePrimeSet Y N) z) + z * S| +
        |z * (Real.log (Real.log Y / Real.log N) - S)| := abs_add_le _ _
    _ ≤ 2 * z ^ 2 / (N : ℝ) + z * (C / Real.log Y + C / Real.log N) := by
      apply add_le_add h₁
      rw [abs_mul, abs_of_nonneg hz, abs_sub_comm, hlog]
      exact mul_le_mul_of_nonneg_left h₂ hz

/-- The all-absent product has the expected logarithmic normalization.
Only Mertens' reciprocal-prime input is used. -/
theorem primeNormalizer_normalized_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (N : ℕ → ℕ) (Y : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (hY : Tendsto Y atTop atTop) (hNY : ∀ᶠ B in atTop, (N B : ℝ) ≤ Y B)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => primeNormalizer (largePrimeSet (Y B) (N B)) z *
      (Real.log (Y B) / Real.log (N B)) ^ z) atTop (𝓝 1) := by
  obtain ⟨C, _, hbound⟩ := primeNormalizer_log_error hM
  have hNreal : Tendsto (fun B => (N B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hlim : Tendsto (fun B => 2 * z ^ 2 / (N B : ℝ) +
      z * (C / Real.log (Y B) + C / Real.log (N B))) atTop (𝓝 0) := by
    have h₁ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * z ^ 2) atTop (𝓝 (2 * z ^ 2))).div_atTop hNreal
    have h₂ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop
      (Real.tendsto_log_atTop.comp hY)
    have h₃ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop
      (Real.tendsto_log_atTop.comp hNreal)
    simpa using h₁.add ((h₂.add h₃).const_mul z)
  let E := fun B => Real.log (primeNormalizer (largePrimeSet (Y B) (N B)) z) +
    z * Real.log (Real.log (Y B) / Real.log (N B))
  have hE : Tendsto E atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [hN.eventually (eventually_ge_atTop 2), hNY] with B hNB hNYB
    simpa [E, Real.norm_eq_abs] using hbound (N B) (Y B) z hNB hNYB hz hz1
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hE
  have heq : (fun B => Real.exp (E B)) =ᶠ[atTop]
      (fun B => primeNormalizer (largePrimeSet (Y B) (N B)) z *
        (Real.log (Y B) / Real.log (N B)) ^ z) := by
    filter_upwards [hN.eventually (eventually_ge_atTop 2), hNY] with B hNB hNYB
    have hN2 : (2 : ℝ) ≤ N B := by exact_mod_cast hNB
    have hlogN : 0 < Real.log (N B) := Real.log_pos (by linarith)
    have hlogY : 0 < Real.log (Y B) := Real.log_pos (by linarith)
    have hprod : 0 < primeNormalizer (largePrimeSet (Y B) (N B)) z := by
      apply prod_pos
      intro p hp
      have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hfrac : z / (p : ℝ) < 1 := (div_lt_one hp0).mpr (by linarith)
      linarith
    dsimp [E]
    rw [Real.exp_add, Real.exp_log hprod,
      Real.rpow_def_of_pos (div_pos hlogY hlogN)]
    congr 1
    congr 1
    ring
  simpa using hexp.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript's auxiliary prime scale

The lower cutoff is `B^1000`, the upper cutoff is `exp (4 B)`, and
`R = B / log (B^1000)`. The normalizing constant below is derived from
the published reciprocal-prime Mertens estimate.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

theorem auxiliaryCutoff_tendsto : Tendsto auxiliaryCutoff atTop atTop :=
  tendsto_pow_atTop (by norm_num : (1000 : ℕ) ≠ 0)

theorem auxiliaryUpper_tendsto : Tendsto auxiliaryUpper atTop atTop :=
  Real.tendsto_exp_atTop.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4))

theorem auxiliaryCutoff_le_upper :
    ∀ᶠ B in atTop, (auxiliaryCutoff B : ℝ) ≤ auxiliaryUpper B := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 1000 (by norm_num : (0 : ℝ) < 4)).def
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with B hB
  have hpow : (0 : ℝ) ≤ (B : ℝ) ^ 1000 := pow_nonneg (Nat.cast_nonneg B) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpow,
    abs_of_pos (Real.exp_pos _), one_mul, auxiliaryCutoff, auxiliaryUpper,
    Nat.cast_pow] using hB

theorem auxiliaryRatio_pos {B : ℕ} (hB : 1 < B) : 0 < auxiliaryRatio B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  exact div_pos (by linarith) (mul_pos (by norm_num) (Real.log_pos hBreal))

theorem auxiliary_log_ratio (B : ℕ) :
    Real.log (auxiliaryUpper B) / Real.log (auxiliaryCutoff B) =
      4 * auxiliaryRatio B := by
  simp only [auxiliaryUpper, Real.log_exp, auxiliaryCutoff, Nat.cast_pow,
    Real.log_pow, auxiliaryRatio]
  ring

/-- The paper's `Q_{z,B} ~ (4 R)^{-z}` in normalized-limit form. -/
theorem auxiliary_primeNormalizer_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => primeNormalizer (auxiliaryPrimes B) z *
      auxiliaryRatio B ^ z) atTop (𝓝 ((4 : ℝ) ^ (-z))) := by
  have h := primeNormalizer_normalized_tendsto hM auxiliaryCutoff auxiliaryUpper
    auxiliaryCutoff_tendsto auxiliaryUpper_tendsto auxiliaryCutoff_le_upper hz hz1
  simp_rw [auxiliary_log_ratio] at h
  have hdiv := h.div_const ((4 : ℝ) ^ z)
  have heq : (fun B => primeNormalizer (largePrimeSet (auxiliaryUpper B)
      (auxiliaryCutoff B)) z * (4 * auxiliaryRatio B) ^ z / (4 : ℝ) ^ z)
      =ᶠ[atTop] (fun B => primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (auxiliaryRatio_pos hB).le]
    change _ = primeNormalizer (largePrimeSet (auxiliaryUpper B) (auxiliaryCutoff B)) z * _
    have hfour : (4 : ℝ) ^ z ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) z).ne'
    field_simp
  simpa [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] using hdiv.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothCorrectionSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The convergent correction series

The finite Euler factors used in removing the small primes are proved
as identities of absolutely convergent series, including at the shifted
exponent required by Rankin's bound.
-/

namespace JointDickman

open Finset

theorem smoothDirichletTerm_mul (E : Finset ℕ) (z s : ℝ) {m n : ℕ}
    (hmn : m.Coprime n) :
    smoothDirichletTerm E z s (m * n) =
      smoothDirichletTerm E z s m * smoothDirichletTerm E z s n := by
  simp only [smoothDirichletTerm, (smoothCorrection_isMultiplicative E z).map_mul_of_coprime hmn,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem smoothDirichletTerm_prime_pow (E : Finset ℕ) (z s : ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    smoothDirichletTerm E z s (p ^ k) =
      (if p ∈ E then -z / (p : ℝ) ^ s else 0) ^ k := by
  by_cases hk : k = 0
  · simp [hk]
  simp only [smoothDirichletTerm, smoothCorrection_prime_pow E z hp hk, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) s,
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  split_ifs <;> simp [div_pow, hk]

theorem smoothDirichletTerm_ratio_lt_one (E : Finset ℕ) {z s : ℝ}
    (hz : |z| < 1) (hs : 0 ≤ s) {p : ℕ} (hp : p.Prime) :
    ‖(if p ∈ E then -z / (p : ℝ) ^ s else 0)‖ < 1 := by
  by_cases hpE : p ∈ E
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ s := Real.one_le_rpow hp1 hs
    simp only [hpE, ite_eq_left, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (Real.rpow_pos_of_pos hp0 s)]
    exact (div_lt_one (Real.rpow_pos_of_pos hp0 s)).mpr (hz.trans_le hpow)
  · simp [hpE]

theorem smoothDirichletTerm_support (E : Finset ℕ) (z s : ℝ) :
    Function.support (smoothDirichletTerm E z s) ⊆ Nat.factoredNumbers E := by
  intro n hn
  rw [Function.mem_support] at hn
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp [smoothDirichletTerm] at hn
  refine ⟨hn0, ?_⟩
  by_contra h
  simp [smoothDirichletTerm, smoothCorrection, hn0, h] at hn

/-- Absolute convergence and the signed Euler-factor identity. -/
theorem smoothCorrection_hasSum (E : Finset ℕ) {z s : ℝ}
    (hz : |z| < 1) (hs : 0 ≤ s) :
    Summable (fun n => ‖smoothDirichletTerm E z s n‖) ∧
      HasSum (smoothDirichletTerm E z s)
        (∏ p ∈ E with p.Prime, (1 + z / (p : ℝ) ^ s)⁻¹) := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k => ‖smoothDirichletTerm E z s (p ^ k)‖) := by
    intro p hp
    simp_rw [smoothDirichletTerm_prime_pow E z s hp]
    exact summable_norm_geometric_of_norm_lt_one
      (smoothDirichletTerm_ratio_lt_one E hz hs hp)
  obtain ⟨hnorm, hsum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      (smoothDirichletTerm_one E z s) (smoothDirichletTerm_mul E z s) hlocal E
  have hsupport := smoothDirichletTerm_support E z s
  have habs_support : Function.support (fun n => ‖smoothDirichletTerm E z s n‖) ⊆
      Nat.factoredNumbers E := by
    intro n hn
    apply hsupport
    simpa only [Function.mem_support, norm_ne_zero_iff] using hn
  refine ⟨((hasSum_subtype_iff_of_support_subset habs_support).mp hnorm.hasSum).summable, ?_⟩
  apply (hasSum_subtype_iff_of_support_subset hsupport).mp
  convert hsum using 1
  all_goals try rfl
  apply prod_congr rfl
  intro p hp
  obtain ⟨_, hprime⟩ := mem_filter.mp hp
  simp_rw [smoothDirichletTerm_prime_pow E z s hprime]
  rw [(hasSum_geometric_of_norm_lt_one
    (smoothDirichletTerm_ratio_lt_one E hz hs hprime)).tsum_eq]
  simp [mem_of_mem_filter p hp, sub_eq_add_neg, neg_div]

/-- The zeroth correction moment is the inverse of the removed local factors. -/
theorem smoothCorrection_zeroth_moment (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun n => smoothCorrection E z n / (n : ℝ))
      (∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹) := by
  have h := (smoothCorrection_hasSum E hz (by norm_num : (0 : ℝ) ≤ 1)).2
  have hf : smoothDirichletTerm E z 1 = fun n => smoothCorrection E z n / (n : ℝ) := by
    funext n
    simp [smoothDirichletTerm]
  rw [hf] at h
  simpa using h

theorem smoothDirichletTerm_abs (E : Finset ℕ) {z : ℝ} (hz : 0 ≤ z)
    (s : ℝ) (n : ℕ) :
    |smoothDirichletTerm E z s n| = smoothDirichletTerm E (-z) s n := by
  simp only [smoothDirichletTerm, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s),
    smoothCorrection, ArithmeticFunction.coe_mk]
  split_ifs <;> simp [abs_pow, abs_neg, abs_of_nonneg hz]

/-- The absolute correction moment is a finite product of positive geometric factors. -/
theorem smoothCorrection_abs_hasSum (E : Finset ℕ) {z s : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hs : 0 ≤ s) :
    HasSum (fun n => |smoothCorrection E z n| / (n : ℝ) ^ s)
      (∏ p ∈ E with p.Prime, (1 - z / (p : ℝ) ^ s)⁻¹) := by
  have hz' : |-z| < 1 := by simpa [abs_of_nonneg hz] using hz1
  have h := (smoothCorrection_hasSum E hz' hs).2
  have hf : smoothDirichletTerm E (-z) s =
      fun n => |smoothCorrection E z n| / (n : ℝ) ^ s := by
    funext n
    rw [← smoothDirichletTerm_abs E hz]
    simp [smoothDirichletTerm, abs_div,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
  rw [hf] at h
  simpa [neg_div, sub_eq_add_neg] using h

/-- An exponential bound for every finite truncation of the absolute series. -/
theorem smoothCorrection_abs_sum_le_exp (E S : Finset ℕ) {z s : ℝ}
    (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (hs : 0 ≤ s) :
    (∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) ^ s) ≤
      Real.exp (2 * z * ∑ p ∈ E with p.Prime, 1 / (p : ℝ) ^ s) := by
  have hsum := smoothCorrection_abs_hasSum E hz (by linarith) hs
  calc
    _ ≤ ∏ p ∈ E with p.Prime, (1 - z / (p : ℝ) ^ s)⁻¹ := by
      rw [← hsum.tsum_eq]
      exact hsum.summable.sum_le_tsum S (fun n _ =>
        div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) s))
    _ ≤ Real.exp (2 * ∑ p ∈ E with p.Prime, z / (p : ℝ) ^ s) := by
      apply inverse_product_le_exp
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_lt.le
      have hpow := Real.one_le_rpow hp1 hs
      refine ⟨div_nonneg hz (by positivity), ?_⟩
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by
      congr 1
      simp only [div_eq_mul_inv, one_mul, ← mul_sum]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMomentBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the moving roughness correction

The exponent shift `1 / log P` costs only a fixed power of `log P`.
This supplies the moment in Rankin's argument from Mertens' estimate,
rather than assuming a cutoff-dependent bound.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem shifted_reciprocal_le {p P : ℝ} (hp : 0 < p) (hpP : p ≤ P)
    (hlog : 0 < Real.log P) :
    1 / p ^ (1 - 1 / Real.log P) ≤ Real.exp 1 / p := by
  have hpow : p ^ (1 / Real.log P) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hp]
    apply Real.exp_le_exp.mpr
    have hle : Real.log p ≤ Real.log P := Real.log_le_log hp hpP
    simpa only [mul_one_div] using (div_le_one hlog).mpr hle
  rw [Real.rpow_sub hp, Real.rpow_one]
  simpa only [one_div_div] using div_le_div_of_nonneg_right hpow hp.le

theorem shifted_prime_sum_le (P : ℕ) (hlog : 0 < Real.log P) :
    (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P)) ≤
      Real.exp 1 * primeReciprocalSum P := by
  simp only [primeReciprocalSum, Nat.floor_natCast, mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpP, hprime⟩ := Nat.mem_primesLE.mp hp
  simpa only [mul_one_div] using shifted_reciprocal_le
    (by exact_mod_cast hprime.pos) (by exact_mod_cast hpP) hlog

/-- Mertens controls the shifted absolute correction moment by a fixed
power of the logarithm, uniformly over all finite truncations. -/
theorem smoothCorrection_shifted_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (S : Finset ℕ) (z : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      (∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| /
        (n : ℝ) ^ (1 - 1 / Real.log P)) ≤
        A * (Real.log P) ^ (Real.exp 1) := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨Real.exp (Real.exp 1 * (|M| + C)), Real.exp_pos _, ?_⟩
  intro P S z hP hlog hz hzhalf
  have hlogpos : 0 < Real.log P := by linarith
  have hshift : 0 ≤ 1 - 1 / Real.log P := by
    have h := (div_le_one hlogpos).mpr hlog
    linarith
  have hMertens : primeReciprocalSum P ≤ Real.log (Real.log P) + |M| + C := by
    have h := (abs_le.mp (hbound P (by exact_mod_cast hP))).2
    have hCdiv : C / Real.log P ≤ C := (div_le_iff₀ hlogpos).mpr (by nlinarith)
    have hMabs := le_abs_self M
    simp only [← primesLE_eq_filter] at h
    change primeReciprocalSum P - Real.log (Real.log P) - M ≤ C / Real.log P at h
    linarith
  have hprime : (Nat.primesLE P).filter Nat.Prime = Nat.primesLE P :=
    filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  calc
    _ ≤ Real.exp (2 * z * ∑ p ∈ Nat.primesLE P,
        1 / (p : ℝ) ^ (1 - 1 / Real.log P)) := by
      simpa only [hprime] using smoothCorrection_abs_sum_le_exp
        (Nat.primesLE P) S hz hzhalf hshift
    _ ≤ Real.exp (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P)) := by
      apply Real.exp_le_exp.mpr
      have hsum : 0 ≤ ∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P) :=
        sum_nonneg (fun p _ => by positivity)
      nlinarith
    _ ≤ Real.exp (Real.exp 1 * primeReciprocalSum P) :=
      Real.exp_le_exp.mpr (shifted_prime_sum_le P hlogpos)
    _ ≤ Real.exp (Real.exp 1 * (Real.log (Real.log P) + |M| + C)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hMertens (Real.exp_pos _).le)
    _ = _ := by
      rw [show Real.exp 1 * (Real.log (Real.log P) + |M| + C) =
        Real.exp 1 * (|M| + C) + Real.log (Real.log P) * Real.exp 1 by ring,
        Real.exp_add, ← Real.rpow_def_of_pos hlogpos]

theorem log_pow_le_rpow (k : ℕ) {v ε : ℝ} (hv : 1 ≤ v) (hε : 0 < ε) :
    (Real.log v) ^ k ≤ ((k.factorial : ℝ) / ε ^ k) * v ^ ε := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h := (div_le_iff₀ hfact).mp
    (Real.pow_div_factorial_le_exp (ε * Real.log v) (mul_nonneg hε.le (Real.log_nonneg hv)) k)
  have hexp : Real.exp (ε * Real.log v) = v ^ ε := by
    rw [Real.rpow_def_of_pos hv0, mul_comm]
  rw [mul_pow, hexp] at h
  calc
    (Real.log v) ^ k ≤ (v ^ ε * (k.factorial : ℝ)) / ε ^ k :=
      (le_div_iff₀ (pow_pos hε k)).mpr (by nlinarith [h])
    _ = _ := by ring

/-- Exponential tilting controls every logarithmic correction moment. -/
theorem smoothCorrection_log_moment_le (E S : Finset ℕ) (k : ℕ)
    (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) * (Real.log n) ^ k) ≤
      ((k.factorial : ℝ) / ε ^ k) *
        ∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) ^ (1 - ε) := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  calc
    _ ≤ (|smoothCorrection E z n| / (n : ℝ)) *
        (((k.factorial : ℝ) / ε ^ k) * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (log_pow_le_rpow k hn1 hε) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]
      field_simp

/-- The absolute constant in the roughness bound works for every fixed
moment order; only the factorial and extra logarithmic power change. -/
theorem smoothCorrection_log_moments_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (S : Finset ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      (∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| / (n : ℝ) *
        (Real.log n) ^ k) ≤
        A * (k.factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + k) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P S z k hP hlog hz hzhalf => ?_⟩
  have hlogpos : 0 < Real.log P := by linarith
  calc
    _ ≤ ((k.factorial : ℝ) / (1 / Real.log P) ^ k) *
        ∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| /
          (n : ℝ) ^ (1 - 1 / Real.log P) :=
      smoothCorrection_log_moment_le _ _ k z (by positivity)
    _ ≤ ((k.factorial : ℝ) / (1 / Real.log P) ^ k) *
        (A * (Real.log P) ^ (Real.exp 1)) :=
      mul_le_mul_of_nonneg_left (hbound P S z hP hlog hz hzhalf) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlogpos, Real.rpow_natCast]
      simp only [one_div, inv_pow, div_inv_eq_mul]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CorrectionMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coefficients' actual logarithmic moments

These are absolutely convergent series of the smooth correction.
The bounds are uniform in the moving cutoff and every fixed moment order.
-/

namespace JointDickman

open Finset

theorem correctionLogTerm_norm (E : Finset ℕ) (z : ℝ) (k n : ℕ) :
    ‖correctionLogTerm E z k n‖ =
      |smoothCorrection E z n| / (n : ℝ) * (Real.log n) ^ k := by
  rw [correctionLogTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)]

theorem correctionLogTerm_summable (E : Finset ℕ) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (k : ℕ) :
    Summable (fun n => ‖correctionLogTerm E z k n‖) := by
  have hbase := (smoothCorrection_abs_hasSum E hz hz1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).summable
  have hdom : Summable (fun n => ((k.factorial : ℝ) / (1 / 2 : ℝ) ^ k) *
      (|smoothCorrection E z n| / (n : ℝ) ^ (1 - (1 / 2 : ℝ)))) := by
    simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      hbase.mul_left ((k.factorial : ℝ) / (1 / 2 : ℝ) ^ k)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hdom
  intro n
  rw [correctionLogTerm_norm]
  simpa using smoothCorrection_log_moment_le E {n} k z (by norm_num : (0 : ℝ) < 1 / 2)

theorem correctionLogMoment_zero (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    correctionLogMoment E z 0 =
      ∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹ := by
  simpa [correctionLogMoment, correctionLogTerm] using
    (smoothCorrection_zeroth_moment E hz).tsum_eq

/-- The fixed-order coefficient moments are bounded with one absolute
logarithmic exponent. -/
theorem correctionLogMoment_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      |correctionLogMoment (Nat.primesLE P) z k| ≤
        A * (k.factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + k) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_log_moments_bound hM
  refine ⟨A, hA, fun P z k hP hlog hz hzhalf => ?_⟩
  have hsum := correctionLogTerm_summable (Nat.primesLE P) hz (by linarith) k
  have hnorm := hsum.tsum_le_of_sum_le (fun S => by
    simpa only [correctionLogTerm_norm] using hbound P S z k hP hlog hz hzhalf)
  calc
    _ = ‖∑' n, correctionLogTerm (Nat.primesLE P) z k n‖ := by
      rw [Real.norm_eq_abs, correctionLogMoment]
    _ ≤ ∑' n, ‖correctionLogTerm (Nat.primesLE P) z k n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ _ := hnorm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients after removal of the small prime factors

Each coefficient is a finite combination of the published fixed-order
Selberg–Delange coefficients and the actual correction moments. The
definition has no dependence on a subsequently chosen truncation order.
-/

namespace JointDickman

open Finset

theorem roughCoefficient_zero (c : ℕ → ℝ) (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    roughCoefficient c E z 0 = c 0 *
      ∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹ := by
  simp [roughCoefficient, correctionLogMoment_zero E hz]

/-- Uniform coefficient bound with the absolute exponent supplied by
the correction moment estimate. -/
theorem roughCoefficient_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (c : ℕ → ℝ)
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (ν : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, 2 ≤ P → 1 ≤ Real.log P →
      |roughCoefficient c (Nat.primesLE P) z ν| ≤
        C * (Real.log P) ^ (Real.exp 1 + ν) := by
  obtain ⟨A, hA, hmom⟩ := correctionLogMoment_bound hM
  let C := ∑ j ∈ range (ν + 1),
    |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| * A * ((ν - j).factorial : ℝ)
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => by positivity)
  refine ⟨C, hC, fun P hP hlog => ?_⟩
  unfold roughCoefficient
  calc
    _ ≤ ∑ j ∈ range (ν + 1),
        |c j * rpowShiftCoeff (z - 1 - j) (ν - j) *
          correctionLogMoment (Nat.primesLE P) z (ν - j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (ν + 1),
        (|c j * rpowShiftCoeff (z - 1 - j) (ν - j)| * A * ((ν - j).factorial : ℝ)) *
          (Real.log P) ^ (Real.exp 1 + ν) := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      have hpow : (Real.log P) ^ (Real.exp 1 + (ν - j : ℕ)) ≤
          (Real.log P) ^ (Real.exp 1 + ν) := by
        apply Real.rpow_le_rpow_of_exponent_le hlog
        have hsub : ((ν - j : ℕ) : ℝ) ≤ ν := by exact_mod_cast Nat.sub_le ν j
        linarith
      calc
        _ ≤ |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| *
            (A * ((ν - j).factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + (ν - j : ℕ))) :=
          mul_le_mul_of_nonneg_left (hmom P z (ν - j) hP hlog hz hzhalf) (abs_nonneg _)
        _ ≤ |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| *
            (A * ((ν - j).factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + ν)) := by
          gcongr
        _ = _ := by ring
    _ = _ := by rw [← sum_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of the squarefree Selberg–Delange Euler factor

Cancellation of the linear local logarithms proves absolute convergence.
This identifies the same Euler product used in the published leading
coefficient, without assuming its convergence as another input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem log_one_add_sub_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-x| < 1 by rw [abs_neg, abs_of_nonneg hx]; linarith) 1
  have hbase : |Real.log (1 + x) - x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_neg, abs_of_nonneg hx, sub_neg_eq_add, sub_eq_add_neg, add_comm] using h
  apply hbase.trans
  apply (div_le_iff₀ (show 0 < 1 - x by linarith)).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem squarefreeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) {p : ℕ} (hp : p.Prime) :
    0 < squarefreeEulerFactor z p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply mul_pos
  · have h := div_nonneg hz hp0.le
    linarith
  · apply Real.rpow_pos_of_pos
    have h := (div_lt_one hp0).mpr hp1
    linarith

theorem squarefreeEulerFactor_log_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {p : ℕ} (hp : p.Prime) :
    |Real.log (squarefreeEulerFactor z p)| ≤ 4 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsub : 0 < 1 - 1 / (p : ℝ) := by
    have h := (div_lt_one hp0).mpr hp1
    linarith
  have hadd : 0 < 1 + z / (p : ℝ) := by positivity
  have hfrac : z / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hrec : 1 / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have h₁ := log_one_add_sub_error (div_nonneg hz hp0.le) hfrac
  have h₂ := log_one_sub_add_error (by positivity : (0 : ℝ) ≤ 1 / p) hrec
  have heq : Real.log (squarefreeEulerFactor z p) =
      (Real.log (1 + z / (p : ℝ)) - z / p) + z *
        (Real.log (1 - 1 / (p : ℝ)) + 1 / p) := by
    rw [squarefreeEulerFactor, Real.log_mul hadd.ne' (Real.rpow_pos_of_pos hsub z).ne',
      Real.log_rpow hsub]
    ring
  rw [heq]
  calc
    _ ≤ |Real.log (1 + z / (p : ℝ)) - z / p| +
        |z * (Real.log (1 - 1 / (p : ℝ)) + 1 / p)| := abs_add_le _ _
    _ ≤ 2 * (z / (p : ℝ)) ^ 2 + z * (2 * (1 / (p : ℝ)) ^ 2) := by
      rw [abs_mul, abs_of_nonneg hz]
      exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hz)
    _ ≤ 4 / (p : ℝ) ^ 2 := by
      have hzsq : z ^ 2 ≤ 1 := by nlinarith
      field_simp
      nlinarith

theorem primeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 < primeEulerFactor z n := by
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn] using squarefreeEulerFactor_pos hz hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_log_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun n => Real.log (primeEulerFactor z n)) := by
  have hsum := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 4
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsum
  intro n
  rw [Real.norm_eq_abs]
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn, mul_one_div] using squarefreeEulerFactor_log_bound hz hz1 hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_multipliable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Multipliable (primeEulerFactor z) :=
  Real.multipliable_of_summable_log (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)

theorem squarefreeEulerProduct_pos {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < ∏' n : ℕ, primeEulerFactor z n := by
  rw [← Real.rexp_tsum_eq_tprod (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)]
  exact Real.exp_pos _

theorem squarefreeEulerProduct_eq (z : ℝ) :
    (∏' n : ℕ, primeEulerFactor z n) =
      ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p := by
  calc
    _ = ∏' n : ℕ, ({p : ℕ | p.Prime}.mulIndicator (squarefreeEulerFactor z)) n := by
      apply tprod_congr
      intro n
      by_cases hn : n.Prime <;> simp [primeEulerFactor, Set.mulIndicator, hn]
    _ = _ := (tprod_subtype {p : ℕ | p.Prime} (squarefreeEulerFactor z)).symm

theorem squarefreeEulerProduct_partial (z : ℝ) (N : ℕ) :
    (∏ n ∈ range (N + 1), primeEulerFactor z n) =
      ∏ p ∈ Nat.primesLE N, squarefreeEulerFactor z p := by
  have hset : (range (N + 1)).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter, mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
  simp only [primeEulerFactor]
  rw [← prod_filter, hset]

theorem squarefreeEulerProduct_partial_tendsto {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun N => ∏ p ∈ Nat.primesLE N, squarefreeEulerFactor z p)
      atTop (𝓝 (∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p)) := by
  have h := (primeEulerFactor_multipliable hz hz1).tendsto_prod_tprod_nat.comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, squarefreeEulerProduct_partial, squarefreeEulerProduct_eq] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughLeadingCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The leading coefficient after the roughness cutoff

Mertens' product theorem and the convergent squarefree Euler factor give
the precise constant `exp(-γ z) / Gamma(z)`.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughLeadingCoefficient_identity {z : ℝ} (hz : 0 ≤ z) (P : ℕ) :
    roughLeadingCoefficient z P * (Real.log P) ^ z =
      (squarefreeLeadingConstant z / ∏ p ∈ Nat.primesLE P, squarefreeEulerFactor z p) *
        (Real.log P * ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) ^ z := by
  let S := Nat.primesLE P
  have hlocal (p : ℕ) (hp : p ∈ S) : 0 < 1 - 1 / (p : ℝ) := by
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    have hh := (div_lt_one hp0).mpr hp1
    linarith
  have hU : 0 < ∏ p ∈ S, (1 - 1 / (p : ℝ)) := prod_pos hlocal
  have hA : 0 < ∏ p ∈ S, (1 + z / (p : ℝ)) := by
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    have hh := div_nonneg hz hp0.le
    linarith
  have hF : (∏ p ∈ S, squarefreeEulerFactor z p) =
      (∏ p ∈ S, (1 + z / (p : ℝ))) * (∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ z := by
    simp only [squarefreeEulerFactor, prod_mul_distrib]
    rw [Real.finsetProd_rpow S _ (fun p hp => (hlocal p hp).le)]
  change (squarefreeLeadingConstant z * ∏ p ∈ S, (1 + z / (p : ℝ))⁻¹) *
    (Real.log P) ^ z = (squarefreeLeadingConstant z / ∏ p ∈ S, squarefreeEulerFactor z p) *
      (Real.log P * ∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ z
  rw [hF, Real.mul_rpow (Real.log_natCast_nonneg P) hU.le, prod_inv_distrib]
  have hUz := (Real.rpow_pos_of_pos hU z).ne'
  field_simp [hA.ne', hUz]

/-- Only the cited Mertens product input is used in this normalization. -/
theorem roughLeadingCoefficient_tendsto
    (hM : PublishedInputs.PrimeProductMertensInput) {z : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) :
    Tendsto (fun P => roughLeadingCoefficient z P * (Real.log P) ^ z) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) := by
  let G := ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p
  have hG : 0 < G := by
    dsimp only [G]
    rw [← squarefreeEulerProduct_eq]
    exact squarefreeEulerProduct_pos hz.le hz1
  have hprod : Tendsto (fun P : ℕ => Real.log P *
      ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa only [← primesLE_eq_filter, Function.comp_def, Nat.floor_natCast] using
      hM.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => squarefreeLeadingConstant z) atTop
      (𝓝 (squarefreeLeadingConstant z))).div
        (squarefreeEulerProduct_partial_tendsto hz.le hz1) hG.ne').mul
          (hprod.rpow_const (Or.inr hz.le))
  have hconstant : squarefreeLeadingConstant z / G *
      Real.exp (-Real.eulerMascheroniConstant) ^ z =
        Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z := by
    change (G / Real.Gamma z) / G * _ = _
    rw [← Real.exp_mul]
    field_simp [hG.ne', (Real.Gamma_pos_of_pos hz).ne']
  rw [hconstant] at h
  exact h.congr' (Eventually.of_forall (fun P => (roughLeadingCoefficient_identity hz.le P).symm))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ScaledRoughCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients in the limiting prime-product density

The zeroth normalized coefficient has the stated limit, and every fixed
higher coefficient vanishes. No residue-distribution assertion is assumed.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primeNormalizer_bounds (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ primeNormalizer E z ∧ primeNormalizer E z ≤ 1 := by
  have hlocal (p : ℕ) (hp : p ∈ E) : 0 ≤ 1 - z / (p : ℝ) ∧ 1 - z / (p : ℝ) ≤ 1 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hE p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hE p hp).one_le
    have hdiv : z / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr (hz1.trans hp1)
    constructor
    · linarith
    · linarith [div_nonneg hz hp0.le]
  exact ⟨prod_nonneg (fun p hp => (hlocal p hp).1),
    Finset.prod_le_one (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2)⟩

theorem roughCoefficient_zero_eq_leading (c : ℕ → ℝ) {z : ℝ}
    (hc : c 0 = squarefreeLeadingConstant z) (hz : |z| < 1) (P : ℕ) :
    roughCoefficient c (Nat.primesLE P) z 0 = roughLeadingCoefficient z P := by
  rw [roughCoefficient_zero c _ hz, hc]
  have hp : (Nat.primesLE P).filter Nat.Prime = Nat.primesLE P :=
    filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  simp only [roughLeadingCoefficient, hp]

theorem auxiliaryRatio_mul_log {B : ℕ} (hB : 1 < B) :
    auxiliaryRatio B * Real.log (auxiliaryCutoff B) = B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hlog : Real.log B ≠ 0 := (Real.log_pos hBreal).ne'
  simp only [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  norm_num
  field_simp

theorem scaledRoughCoefficient_zero_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hz1 : z < 1) :
    Tendsto (fun B => scaledRoughCoefficient c z 0 B) atTop
      (𝓝 ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z))) := by
  have hlead := (roughLeadingCoefficient_tendsto hMP hz hz1.le).comp auxiliaryCutoff_tendsto
  have h := (auxiliary_primeNormalizer_tendsto hM hz.le hz1.le).mul hlead
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hR : 0 ≤ auxiliaryRatio B := (auxiliaryRatio_pos hB).le
  have hlog : 0 ≤ Real.log (auxiliaryCutoff B) := Real.log_natCast_nonneg _
  have hpow : (auxiliaryRatio B) ^ z * (Real.log (auxiliaryCutoff B)) ^ z = (B : ℝ) ^ z := by
    rw [← Real.mul_rpow hR hlog, auxiliaryRatio_mul_log hB]
  unfold scaledRoughCoefficient
  rw [Nat.cast_zero, sub_zero,
    roughCoefficient_zero_eq_leading c hc (by rwa [abs_of_pos hz])]
  dsimp only [Function.comp_def]
  rw [mul_mul_mul_comm, hpow]

theorem scaledRoughCoefficient_succ_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (j : ℕ) :
    Tendsto (fun B => scaledRoughCoefficient c z (j + 1) B) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := roughCoefficient_bound hM c hz hzhalf (j + 1)
  let a : ℝ := (j + 1 : ℕ) - z
  let r : ℝ := Real.exp 1 + (j + 1 : ℕ)
  have ha : 0 < a := by dsimp [a]; push_cast <;> linarith [Nat.cast_nonneg j (α := ℝ)]
  have hlimit := ((log_power_div_power_tendsto_zero r ha).const_mul
    (C * (1000 : ℝ) ^ r)).comp tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlimit
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlimit
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlogP : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hP, hlogP, eventually_gt_atTop 1] with B hp hlog hB
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hQ := primeNormalizer_bounds _ (auxiliaryPrimes_prime B) hz (by linarith : z ≤ 1)
  have hb := hbound (auxiliaryCutoff B) hp hlog
  rw [Real.norm_eq_abs, scaledRoughCoefficient, abs_mul, abs_mul,
    abs_of_nonneg hQ.1, abs_of_pos (Real.rpow_pos_of_pos hB0 _)]
  calc
    _ ≤ 1 * (C * (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (j + 1 : ℕ))) *
        (B : ℝ) ^ (z - (j + 1 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hQ.2 hb (abs_nonneg _) (by norm_num)) (Real.rpow_nonneg hB0.le _)
    _ = C * (1000 : ℝ) ^ r * ((Real.log B) ^ r / (B : ℝ) ^ a) := by
      have hcut : Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
        simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow] <;> norm_num
      rw [one_mul, hcut, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_pos hBreal).le]
      have hexp : z - (j + 1 : ℕ) = -a := by dsimp [a] <;> ring
      rw [hexp, Real.rpow_neg hB0.le]
      dsimp [r]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform convergence of the prime-product density

Finite combinations of the actual rough coefficients converge uniformly
away from zero. This is the smooth density used for the coarse channel.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem scaledRoughDensity_eq (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    scaledRoughDensity c z H B s =
      B * primeNormalizer (auxiliaryPrimes B) z *
        roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (B * s) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  unfold scaledRoughDensity roughDensityPolynomial
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j _
  unfold scaledRoughCoefficient
  have hfirst : (B : ℝ) ^ (z - j) = B * (B : ℝ) ^ (z - 1 - j) := by
    rw [show z - (j : ℝ) = 1 + (z - 1 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  have hsecond : (B : ℝ) ^ (z - 1 - j) = B * (B : ℝ) ^ (z - 2 - j) := by
    rw [show z - 1 - (j : ℝ) = 1 + (z - 2 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  rw [Real.mul_rpow hB0.le hs.le, Real.mul_rpow hB0.le hs.le, hfirst]
  have hBn : (B : ℝ) ≠ 0 := hB0.ne'
  field_simp
  rw [hsecond]
  ring

/-- A coefficient limit gives a uniform limit for a fixed negative power. -/
theorem scalar_power_uniform {a δ c : ℝ} {u : ℕ → ℝ}
    (ha : a ≤ 0) (hδ : 0 < δ) (hu : Tendsto u atTop (𝓝 c)) :
    TendstoUniformlyOn (fun (B : ℕ) (s : ℝ) => u B * s ^ a)
      (fun s => c * s ^ a) atTop (Set.Ici δ) := by
  have hnorm : Tendsto (fun n : ℕ => |u n - c| * δ ^ a) atTop (𝓝 0) := by
    simpa using ((hu.sub_const c).abs.mul_const (δ ^ a))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall := hnorm.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with B hB
  intro s hs
  have hs0 : 0 < s := hδ.trans_le hs
  have hp := Real.rpow_le_rpow_of_nonpos hδ hs ha
  calc
    dist (c * s ^ a) (u B * s ^ a) = |u B - c| * s ^ a := by
      rw [Real.dist_eq, ← sub_mul, abs_mul, abs_sub_comm,
        abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    _ ≤ |u B - c| * δ ^ a := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ < ε := hB

/-- Finite fixed powers preserve uniform convergence of their coefficients. -/
theorem finite_power_uniform (S : Finset ℕ) (a c : ℕ → ℝ) (u : ℕ → ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (ha : ∀ j ∈ S, a j ≤ 0)
    (hu : ∀ j ∈ S, Tendsto (fun B => u B j) atTop (𝓝 (c j))) :
    TendstoUniformlyOn (fun B s => ∑ j ∈ S, u B j * s ^ a j)
      (fun s => ∑ j ∈ S, c j * s ^ a j) atTop (Set.Ici δ) := by
  induction S using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const (Set.Ici δ)
  | @insert i S hi ih =>
      have hfirst := scalar_power_uniform (ha i (mem_insert_self i S)) hδ (hu i (mem_insert_self i S))
      have hrest := ih (fun j hj => ha j (mem_insert_of_mem hj))
        (fun j hj => hu j (mem_insert_of_mem hj))
      convert hfirst.add hrest using 1 <;> first | (with_reducible_and_instances rfl) | (ext <;> simp [sum_insert hi])

/-- The density converges uniformly on every interval bounded away from zero.
The stronger half-line statement is available because all exponents are negative. -/
theorem scaledRoughDensity_tendstoUniformlyOn
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    TendstoUniformlyOn (fun B s => scaledRoughDensity c z H B s)
      (fun s => ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) * s ^ (z - 1))
      atTop (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hfirst := finite_power_uniform (range (H + 1)) (fun j => z - 1 - j) b
    (fun B j => scaledRoughCoefficient c z j B) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => hcoef j)
  have hsecond := finite_power_uniform (range (H + 1)) (fun j => z - 2 - j) (fun _ => 0)
    (fun B j => scaledRoughCoefficient c z j B / B * (z - 1 - j)) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => by
      simpa using ((hcoef j).div_atTop tendsto_natCast_atTop_atTop).mul_const (z - 1 - j))
  convert hfirst.add hsecond using 1
  · rfl
  · funext s
    simp [b, k]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Derivatives of the density used in partial summation

The finite model is differentiated directly, and its first derivative
converges uniformly away from zero along with the density itself.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem hasDerivAt_scaledRoughDensity (c : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (scaledRoughDensity c z H B) (scaledRoughDensityDeriv c z H B s) s := by
  have hfirst : ∀ j ∈ range (H + 1),
      HasDerivAt (fun t => scaledRoughCoefficient c z j B * t ^ (z - 1 - j))
        ((scaledRoughCoefficient c z j B * (z - 1 - j)) * s ^ (z - 2 - j)) s := by
    intro j _
    convert (Real.hasDerivAt_rpow_const (p := z - 1 - j) (Or.inl hs.ne')).const_mul
      (scaledRoughCoefficient c z j B) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show z - 1 - (j : ℝ) - 1 = z - 2 - j by ring]
    ring
  have hsecond : ∀ j ∈ range (H + 1),
      HasDerivAt (fun t => (scaledRoughCoefficient c z j B / B * (z - 1 - j)) * t ^ (z - 2 - j))
        ((scaledRoughCoefficient c z j B / B * (z - 1 - j) * (z - 2 - j)) * s ^ (z - 3 - j)) s := by
    intro j _
    convert (Real.hasDerivAt_rpow_const (p := z - 2 - j) (Or.inl hs.ne')).const_mul
      (scaledRoughCoefficient c z j B / B * (z - 1 - j)) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show z - 2 - (j : ℝ) - 1 = z - 3 - j by ring]
    ring
  exact (HasDerivAt.fun_sum hfirst).add (HasDerivAt.fun_sum hsecond)

theorem scaledRoughDensityDeriv_tendstoUniformlyOn
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    TendstoUniformlyOn (fun B s => scaledRoughDensityDeriv c z H B s)
      (fun s => ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) *
          (z - 1) * s ^ (z - 2)) atTop (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hfirst := finite_power_uniform (range (H + 1)) (fun j => z - 2 - j)
    (fun j => b j * (z - 1 - j)) (fun B j => scaledRoughCoefficient c z j B * (z - 1 - j))
    hδ (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)])
    (fun j _ => (hcoef j).mul_const _)
  have hsecond := finite_power_uniform (range (H + 1)) (fun j => z - 3 - j) (fun _ => 0)
    (fun B j => scaledRoughCoefficient c z j B / B * (z - 1 - j) * (z - 2 - j)) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => by
      simpa using (((hcoef j).div_atTop tendsto_natCast_atTop_atTop).mul_const
        (z - 1 - j)).mul_const (z - 2 - j))
  convert hfirst.add hsecond using 1
  · rfl
  · funext s
    simp [b, k]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual arithmetic coefficient weight A₀ -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_nonneg (B : ℕ) : 0 ≤ coefficientScale B := by
  unfold coefficientScale
  exact mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B))) _)

theorem coefficientWeight_nonneg (B n : ℕ) : 0 ≤ coefficientWeight B n := by
  have hs := coefficientScale_nonneg B
  unfold coefficientWeight roughSquarefreeWeight squarefreeWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform boundedness and Lipschitz control of the actual density

These estimates provide the profile hypotheses in the coarse channel.
Their constants are independent of the auxiliary integer B.
-/

namespace JointDickman

open Filter
open scoped Topology NNReal

theorem uniform_power_eventually_bounded {u : ℕ → ℝ → ℝ} {k a δ : ℝ}
    (hδ : 0 < δ) (ha : a ≤ 0)
    (hu : TendstoUniformlyOn u (fun s => k * s ^ a) atTop (Set.Ici δ)) :
    ∀ᶠ B : ℕ in atTop, ∀ s ∈ Set.Ici δ, |u B s| ≤ |k| * δ ^ a + 1 := by
  have h := (Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)
  filter_upwards [h] with B hB
  intro s hs
  have hs0 : 0 < s := hδ.trans_le hs
  have hdist := hB s hs
  rw [Real.dist_eq] at hdist
  have hpow := Real.rpow_le_rpow_of_nonpos hδ hs ha
  calc
    |u B s| = |(u B s - k * s ^ a) + k * s ^ a| := by congr 1; ring
    _ ≤ |u B s - k * s ^ a| + |k * s ^ a| := abs_add_le _ _
    _ = |k * s ^ a - u B s| + |k| * s ^ a := by
      rw [abs_sub_comm, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    _ ≤ |k| * δ ^ a + 1 := by nlinarith [mul_le_mul_of_nonneg_left hpow (abs_nonneg k)]

theorem scaledRoughDensity_bounded_lipschitz
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
      (∀ s ∈ Set.Ici δ, |scaledRoughDensity c z H B s| ≤ M) ∧
      LipschitzOnWith L (scaledRoughDensity c z H B) (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let M := |k| * δ ^ (z - 1) + 1
  let L : ℝ≥0 := ⟨|k * (z - 1)| * δ ^ (z - 2) + 1, by positivity⟩
  have hfun := uniform_power_eventually_bounded hδ (by linarith : z - 1 ≤ 0)
    (scaledRoughDensity_tendstoUniformlyOn hM hMP c hc hz hzhalf hδ H)
  have hder := uniform_power_eventually_bounded hδ (by linarith : z - 2 ≤ 0)
    (scaledRoughDensityDeriv_tendstoUniformlyOn hM hMP c hc hz hzhalf hδ H)
  refine ⟨M, by dsimp [M] <;> positivity, L, ?_⟩
  filter_upwards [hfun, hder] with B hf hd
  refine ⟨hf, ?_⟩
  apply (convex_Ici δ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_scaledRoughDensity c z H B (hδ.trans_le hs)).hasDerivWithinAt)
  intro s hs
  change ‖scaledRoughDensityDeriv c z H B s‖₊ ≤ L
  exact_mod_cast hd s hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AmplificationSmoothCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth cutoff equal to one on the positive interior rectangle -/

namespace JointDickman
open Finset

theorem amplificationBump_bounds (x : ℝ) : 0 ≤ amplificationBump x ∧ amplificationBump x ≤ 1 :=
  ⟨amplificationBump.nonneg, amplificationBump.le_one⟩

theorem amplificationBump_zero {x : ℝ} (hx : x ≤ 1 ∨ 2 ≤ x) : amplificationBump x = 0 := by
  apply amplificationBump.zero_of_le_dist
  change (1/4 : ℝ) ≤ dist x (11/8 : ℝ)
  rw [Real.dist_eq]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem amplificationBump_support {x : ℝ} (hx : amplificationBump x ≠ 0) : 1 < x ∧ x < 2 := by
  constructor
  · by_contra h
    exact hx (amplificationBump_zero (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hx (amplificationBump_zero (Or.inr (le_of_not_gt h)))

theorem amplificationBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => amplificationBump x) :=
  amplificationBump.contDiff

theorem amplificationBump_compactSupport : HasCompactSupport (fun x => amplificationBump x) :=
  amplificationBump.hasCompactSupport

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteAdditiveOrthogonality
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite additive orthogonality for the arithmetic kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped ComplexConjugate

theorem integral_additivePhase_int (k : ℤ) :
    (∫ θ in (0 : ℝ)..1, additivePhase ((k : ℝ)*θ)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk,additivePhase]
  · have hc : (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hk)
        (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    have he : (fun θ : ℝ => additivePhase ((k : ℝ)*θ)) =
        (fun θ : ℝ => Complex.exp ((k : ℂ)*(2*(Real.pi : ℂ)*Complex.I)*θ)) := by
      funext θ
      unfold additivePhase
      congr 1
      push_cast
      ring
    rw [he,integral_exp_mul_complex hc]
    simp [hk,Complex.exp_int_mul_two_pi_mul_I]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMeanNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalization of rough summatory means -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughMeanNormalization_ratio {B : ℕ} (hB : 1 < B) (z : ℝ) :
    roughMeanNormalization B z / (B : ℝ) = 1 / auxiliaryRatio B ^ z := by
  have hR := auxiliaryRatio_pos hB
  have hmul := auxiliaryRatio_mul_log hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hB)
  have hrpow : auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    simp
  unfold roughMeanNormalization
  apply (div_eq_div_iff hB0 (Real.rpow_pos_of_pos hR z).ne').mpr
  calc
    _ = Real.log (auxiliaryCutoff B) *
        (auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z) := by ring
    _ = B := by rw [hrpow, mul_comm, hmul]
    _ = _ := by ring

theorem roughMeanNormalization_quotient_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => roughMeanNormalization B z /
      (primeNormalizer (auxiliaryPrimes B) z * B)) atTop (𝓝 ((4 : ℝ) ^ z)) := by
  have hlim := (auxiliary_primeNormalizer_tendsto hM hz hz1).inv₀
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (-z)).ne'
  have heq : (fun B => (primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z)⁻¹) =ᶠ[atTop]
      (fun B => roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    conv_rhs => rw [mul_comm (primeNormalizer (auxiliaryPrimes B) z)]
    rw [div_mul_eq_div_div, roughMeanNormalization_ratio hB]
    ring
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] at hlim
  simpa only [inv_inv] using hlim.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First and second moments of the actual coefficient A₀

These are the estimates in equation (5) of the manuscript.  The two
specializations of the published Selberg–Delange input suffice here.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_eq_roughMeanNormalization (B : ℕ) :
    coefficientScale B = roughMeanNormalization B (1 / 2) := by
  norm_num [coefficientScale, roughMeanNormalization]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FairSplitChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite fair-split channel

A site is a vector of independent Bernoulli bits. Conditional on that site,
each present prime is retained independently with probability one half and
each absent prime stays absent. Integrating two conditionally independent
retentions gives exactly the same-site two-split law, including for arbitrary
output cells. This connects that law to the actual finite channel kernel.
-/

namespace JointDickman

open scoped BigOperators

theorem fairRetentionBitMass_nonneg (hit retained : Bool) :
    0 ≤ fairRetentionBitMass hit retained := by
  cases hit <;> cases retained <;> norm_num [fairRetentionBitMass, bernoulliBitMass]

theorem fairRetentionBitMass_sum (hit : Bool) : ∑ retained, fairRetentionBitMass hit retained = 1 := by
  cases hit <;> norm_num [fairRetentionBitMass, bernoulliBitMass, Fintype.sum_bool]

theorem fairRetentionBitMass_marginal (q : ℝ) (b : Bool) :
    (∑ hit, bernoulliBitMass q hit * fairRetentionBitMass hit b) = bernoulliBitMass (q / 2) b := by
  cases b <;> simp [fairRetentionBitMass, bernoulliBitMass] <;> ring

theorem fairRetentionMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) : 0 ≤ fairRetentionMass x y :=
  finiteProductMass_nonneg _ (fun i => fairRetentionBitMass_nonneg (x i)) y

theorem fairRetentionMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) : ∑ y, fairRetentionMass x y = 1 :=
  finiteProductMass_sum _ (fun i => fairRetentionBitMass_sum (x i))

theorem bernoulliSiteMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) : ∑ x, bernoulliSiteMass q x = 1 :=
  finiteProductMass_sum _ (fun i => bernoulliBitMass_sum (q i))

theorem bernoulliSiteMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (x : ι → Bool) :
    0 ≤ bernoulliSiteMass q x :=
  finiteProductMass_nonneg _ (fun i => bernoulliBitMass_nonneg (hq i)) x

theorem fairRetentionMass_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → Bool) :
    (∑ x, bernoulliSiteMass q x * fairRetentionMass x y) =
      bernoulliSiteMass (fun i => q i / 2) y := by
  classical
  simp only [bernoulliSiteMass, fairRetentionMass, finiteProductMass, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i hit => bernoulliBitMass (q i) hit *
    fairRetentionBitMass hit (y i))]
  simp_rw [fairRetentionBitMass_marginal]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetThinning
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair thinning of an independently selected prime set -/

namespace JointDickman

open Finset

theorem fairRetentionMass_subsets {α : Type*} [DecidableEq α]
    (P : Finset α) (S T : P.powerset) :
    fairRetentionMass (subsetHitEquiv P S) (subsetHitEquiv P T) =
      subsetRetentionMass S.val T.val := by
  classical
  have heq : fairRetentionMass (subsetHitEquiv P S) (subsetHitEquiv P T) =
      ∏ p ∈ P, if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1 := by
    unfold fairRetentionMass finiteProductMass
    calc
      _ = ∏ p : P, if p.val ∈ S.val then (1 / 2 : ℝ) else if p.val ∈ T.val then 0 else 1 := by
        apply prod_congr rfl
        intro p _
        by_cases hs : p.val ∈ S.val <;> by_cases ht : p.val ∈ T.val <;>
          norm_num [subsetHitEquiv, fairRetentionBitMass, bernoulliBitMass, hs, ht]
      _ = _ := prod_coe_sort P (fun p => if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1)

  rw [heq]
  by_cases ht : T.val ⊆ S.val
  · rw [subsetRetentionMass, ite_eq_left ht]
    have hp (p : α) : (if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1) =
        if p ∈ S.val then (1 / 2 : ℝ) else 1 := by
      by_cases hs : p ∈ S.val
      · simp [hs]
      · have hn : p ∉ T.val := fun h => hs (ht h)
        simp [hs, hn]
    simp_rw [hp]
    rw [← prod_filter]
    have hf : P.filter (fun p => p ∈ S.val) = S.val := by
      ext p
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hp => (mem_powerset.mp S.property) hp)
    rw [hf, prod_const]
  · rw [subsetRetentionMass, ite_eq_right ht]
    obtain ⟨p, hpT, hpS⟩ := not_subset.mp ht
    apply prod_eq_zero (mem_powerset.mp T.property hpT)
    simp only [hpT, hpS, ite_false, if_false, ite_true, if_true]

theorem subsetRetentionMass_marginal {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) {T : Finset α} (hT : T ⊆ P) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * subsetRetentionMass S T) =
      bernoulliSubsetMass P (fun p => q p / 2) T := by
  classical
  let t : P.powerset := ⟨T, mem_powerset.mpr hT⟩
  have h := fairRetentionMass_marginal (fun p : P => q p.val) (subsetHitEquiv P t)
  rw [← (subsetHitEquiv P).sum_comp] at h
  change (∑ s : P.powerset,
    finiteProductMass (fun p : P => bernoulliBitMass (q p.val)) (subsetHitEquiv P s) *
      fairRetentionMass (subsetHitEquiv P s) (subsetHitEquiv P t)) =
    finiteProductMass (fun p : P => bernoulliBitMass (q p.val / 2)) (subsetHitEquiv P t) at h
  simp_rw [bernoulliSubsetMass_eq_product, fairRetentionMass_subsets] at h
  rw [bernoulliSubsetMass_eq_product P (fun p => q p / 2) t] at h
  exact (sum_coe_sort P.powerset (fun S => bernoulliSubsetMass P q S * subsetRetentionMass S T)).symm.trans h

/-- Integrating both the first remaining set and its fair second coins
leaves precisely the independent addition law with halved parameters. -/
theorem subsetRetentionMass_expectation {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (F : Finset α → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S *
      ∑ T ∈ P.powerset, subsetRetentionMass S T * F T) =
      ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => q p / 2) T * F T := by
  classical
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  rw [← sum_mul, subsetRetentionMass_marginal P q (mem_powerset.mp hT)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedSplitProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed fair-split product law used by the kernel -/

namespace JointDickman
open Finset

theorem splitProductMass_nonneg (P S : Finset ℕ) (n : ℕ) :
    0 ≤ splitProductMass P S n := by
  classical
  apply sum_nonneg
  intro A _
  unfold subsetRetentionMass
  split_ifs <;> positivity

theorem signedSplitProductMass_one (P : Finset ℕ) (n : ℕ) :
    signedSplitProductMass P (fun _ => 1) n = primeProductMass P (1/2) n := by
  classical
  unfold signedSplitProductMass splitProductMass
  simp only [mul_one]
  rw [subsetRetentionMass_expectation]
  unfold primeProductMass
  apply sum_congr rfl
  intro A _
  have hq : (fun p : ℕ => (1/(p : ℝ))/2) = (fun p : ℕ => (1/2 : ℝ)/(p : ℝ)) := by
    funext p
    ring
  rw [hq]
  split_ifs <;> simp

theorem signedSplitProductMass_abs_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : Finset ℕ → ℝ} (hg : ∀ S ⊆ P, |g S| ≤ 1) (n : ℕ) :
    |signedSplitProductMass P g n| ≤ primeProductMass P (1/2) n := by
  classical
  rw [← signedSplitProductMass_one]
  unfold signedSplitProductMass
  calc
    _ ≤ ∑ S ∈ P.powerset,
        |bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S * splitProductMass P S n| :=
      abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro S hS
      have hmass : 0 ≤ bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S := by
        apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
        exact ⟨by positivity,(div_le_one (by linarith)).mpr hp1⟩
      rw [abs_mul,abs_mul,abs_of_nonneg hmass,abs_of_nonneg (splitProductMass_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hg S (mem_powerset.mp hS)) hmass)
        (splitProductMass_nonneg _ _ _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CompactOscillatorySupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing finite cutoffs for compactly supported tests -/

namespace JointDickman

open Finset MeasureTheory

open Classical in
theorem tsum_eq_Ioc_of_scaled_support {w : ℝ → ℝ} {a b X : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hX : 0 < X)
    (hws : ∀ t, t ≤ a ∨ b < t → w t = 0)
    (f : ℕ → ℂ) (hf : ∀ n : ℕ, w (n / X) = 0 → f n = 0) :
    ∑' n, f n = ∑ n ∈ Ioc ⌊a * X⌋₊ ⌊b * X⌋₊, f n := by
  apply tsum_eq_sum
  intro n hn
  apply hf n
  apply hws
  by_cases hna : n ≤ ⌊a * X⌋₊
  · left
    exact (div_le_iff₀ hX).mpr ((Nat.le_floor_iff (mul_nonneg ha hX.le)).mp hna)
  · right
    have hnb : ⌊b * X⌋₊ < n := by
      have hn' : ¬(⌊a * X⌋₊ < n ∧ n ≤ ⌊b * X⌋₊) := by simpa only [mem_Ioc] using hn
      omega
    exact (lt_div_iff₀ hX).mpr ((Nat.floor_lt (mul_nonneg (ha.trans hab) hX.le)).mp hnb)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteKernelOrthogonality
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Fourier representation of the finite equation a-b=jc -/

namespace JointDickman
open Finset MeasureTheory

theorem integral_additive_triple (a b c j : ℕ) (u v w : ℂ) :
    (∫ θ in (0 : ℝ)..1,
      (u*additivePhase ((a : ℝ)*θ)) * (v*additivePhase ((b : ℝ)*(-θ))) *
        (w*additivePhase ((c : ℝ)*(-(j : ℝ)*θ)))) =
      if a = b+j*c then u*v*w else 0 := by
  have he : (fun θ : ℝ =>
      (u*additivePhase ((a : ℝ)*θ)) * (v*additivePhase ((b : ℝ)*(-θ))) *
        (w*additivePhase ((c : ℝ)*(-(j : ℝ)*θ)))) =
      (fun θ : ℝ => (u*v*w)*additivePhase (((a : ℤ)-b-(j : ℤ)*c : ℤ)*θ)) := by
    funext θ
    have hp : additivePhase (((a : ℤ)-b-(j : ℤ)*c : ℤ)*θ) =
        additivePhase ((a : ℝ)*θ)*additivePhase ((b : ℝ)*(-θ))*
          additivePhase ((c : ℝ)*(-(j : ℝ)*θ)) := by
      rw [← additivePhase_add,← additivePhase_add]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [he,intervalIntegral.integral_const_mul,integral_additivePhase_int]
  have hz : (a : ℤ)-b-(j : ℤ)*c = 0 ↔ a = b+j*c := by
    rw [← Int.natCast_mul]
    omega
  by_cases h : a = b+j*c
  · simp [h]
  · simp [h,mt hz.mp h]

/-- The finite sum and integral are identical, before any arc is discarded. -/
theorem finiteKernel_orthogonality (A B C : Finset ℕ) (u v w : ℕ → ℂ) (j : ℕ) :
    (∫ θ in (0 : ℝ)..1,
      finiteAdditiveSum A u θ * finiteAdditiveSum B v (-θ) *
        finiteAdditiveSum C w (-(j : ℝ)*θ)) =
      ∑ c ∈ C, ∑ b ∈ B, ∑ a ∈ A, if a = b+j*c then u a*v b*w c else 0 := by
  have hc (a b c : ℕ) : Continuous (fun θ : ℝ =>
      (u a*additivePhase ((a : ℝ)*θ))*(v b*additivePhase ((b : ℝ)*(-θ)))*
        (w c*additivePhase ((c : ℝ)*(-(j : ℝ)*θ)))) := by
    apply Continuous.mul
    · apply Continuous.mul
      · exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))
      · exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_neg))
    · exact continuous_const.mul (continuous_additivePhase.comp
        (continuous_const.mul (continuous_const.mul continuous_id)))
  simp only [finiteAdditiveSum,mul_sum,sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro c _
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro b _
      rw [intervalIntegral.integral_finsetSum]
      · apply sum_congr rfl
        intro a _
        exact integral_additive_triple a b c j (u a) (v b) (w c)
      · intro a _
        exact (hc a b c).intervalIntegrable 0 1
    · intro b _
      apply Continuous.intervalIntegrable
      apply continuous_finsetSum
      intro a _
      exact hc a b c
  · intro c _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro b _
    apply continuous_finsetSum
    intro a _
    exact hc a b c

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDensityBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform boundedness of the actual A0 density away from zero -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem auxiliary_half_normalizer_pos (B : ℕ) :
    0 < primeNormalizer (auxiliaryPrimes B) (1/2) := by
  unfold primeNormalizer
  apply prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
  exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < p)).mpr (by norm_num <;> linarith))

theorem coefficientDensity_eq_scaled (c : ℕ → ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    coefficientDensity c H B s =
      (coefficientScale B / (primeNormalizer (auxiliaryPrimes B) (1/2)*B))*
        scaledRoughDensity c (1/2) H B s := by
  rw [scaledRoughDensity_eq c (1/2) H B hB hs]
  unfold coefficientDensity
  have hQ := (auxiliary_half_normalizer_pos B).ne'
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDensityRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Lipschitz control of the coefficient density -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficientDensity_bounded_lipschitz
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    {δ : ℝ} (hδ : 0 < δ) (H : ℕ) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ ∀ᶠ B : ℕ in atTop,
      (∀ s : ℝ, δ ≤ s → |coefficientDensity c H B s| ≤ M) ∧
      (∀ s t : ℝ, δ ≤ s → δ ≤ t →
        |coefficientDensity c H B s-coefficientDensity c H B t| ≤ L*|s-t|) := by
  obtain ⟨M,hM0,L,hbound⟩ := scaledRoughDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1/2) hδ H
  let J : ℝ := (4 : ℝ)^(1/2 : ℝ)+1
  have hJ : 0 ≤ J := by dsimp [J] <;> positivity
  have hquot : ∀ᶠ B : ℕ in atTop,
      |coefficientScale B/(primeNormalizer (auxiliaryPrimes B) (1/2)*B)| ≤ J := by
    have hh := (roughMeanNormalization_quotient_tendsto hM
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).abs
    have hpos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (1/2 : ℝ)
    have he := hh.eventually (eventually_le_nhds (lt_add_one |(4 : ℝ)^(1/2 : ℝ)|))
    simpa only [← coefficientScale_eq_roughMeanNormalization,abs_of_pos hpos] using he
  refine ⟨J*M,J*(L : ℝ),mul_nonneg hJ hM0,mul_nonneg hJ L.coe_nonneg,?_⟩
  filter_upwards [hbound,hquot,eventually_gt_atTop 0] with B hboundB hquotB hB
  constructor
  · intro s hs
    rw [coefficientDensity_eq_scaled c H B hB (hδ.trans_le hs),abs_mul]
    exact mul_le_mul hquotB (hboundB.1 s hs) (abs_nonneg _) hJ
  · intro s t hs ht
    rw [coefficientDensity_eq_scaled c H B hB (hδ.trans_le hs),
      coefficientDensity_eq_scaled c H B hB (hδ.trans_le ht),← mul_sub,abs_mul]
    have hh := hboundB.2.dist_le_mul s hs t ht
    rw [Real.dist_eq,Real.dist_eq] at hh
    calc
      _ ≤ J*((L : ℝ)*|s-t|) := mul_le_mul hquotB hh (abs_nonneg _) hJ
      _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_LowExclusiveKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite low-exclusive kernel

The common variable and the two exclusive variables have independent
finite masses. Cells are specified by an `Option`-valued map, allowing
discarded outputs. Restricting the second exclusive variable to `low`
has separate row and column estimates, proved from these actual masses.
-/

namespace JointDickman

open scoped BigOperators

section

variable {C E A : Type*} [Fintype C] [Fintype E] [Fintype A] [DecidableEq A]

omit [Fintype A] in
theorem optionCellMass_nonneg (v : E → ℝ) (cell : E → Option A)
    (hv : ∀ e, 0 ≤ v e) (a : A) : 0 ≤ optionCellMass v cell a := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> [exact hv e; exact le_rfl]

theorem optionCellMass_sum_le (v : E → ℝ) (cell : E → Option A)
    (hv : ∀ e, 0 ≤ v e) : (∑ a, optionCellMass v cell a) ≤ ∑ e, v e := by
  unfold optionCellMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e _
  cases h : cell e with
  | none => simpa [h] using hv e
  | some a => simp

end

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeResidueChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite residue estimate for the actual fair-prime channel

This combines the actual two-split comparison, the independent low/high
decomposition, and the exclusive local law. The conclusion concerns the
original fair-split channel and every real input simultaneously.
-/

namespace JointDickman

open scoped BigOperators

theorem fullPrimeMass_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (x : Q → Bool) :
    0 ≤ fullPrimeMass Q x := by
  apply bernoulliSiteMass_nonneg
  intro p
  have hp := hQ p.val p.property
  have hp₀ : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
  exact ⟨by positivity, (div_le_one hp₀).mpr hp₁⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PartialPrimeChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair-prime channels restricted to a collection of output cells -/

namespace JointDickman

open scoped BigOperators

theorem partialFairPrimeTransition_nonneg {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (x : Q → Bool) (a : A) :
    0 ≤ partialFairPrimeTransition Q cell x a :=
  optionCellMass_nonneg _ _ (fairRetentionMass_nonneg x) a

theorem partialFairPrimeTransition_sum_le {A : Type*} [Fintype A] [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (x : Q → Bool) :
    (∑ a, partialFairPrimeTransition Q cell x a) ≤ 1 := by
  have h := optionCellMass_sum_le (fairRetentionMass x) (fun y => cell (retainedPrimeProduct Q y))
    (fairRetentionMass_nonneg x)
  simpa only [partialFairPrimeTransition, fairRetentionMass_sum] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ChannelGrid
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's refining logarithmic grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem channelFineCount_pos {m₁ B : ℕ} (hm : 0 < m₁) (hB : 0 < B) :
    0 < channelFineCount m₁ B := by
  apply Nat.mul_pos hm
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast hB) _))
    (by exact_mod_cast hm)

theorem channelMesh_pos {n : ℕ} (hn : 0 < n) : 0 < channelMesh n :=
  div_pos (by norm_num) (by exact_mod_cast hn)

theorem channel_width (n : ℕ) (i : Fin n) : channelUpper n i - channelLower n i = channelMesh n := by
  unfold channelUpper channelLower
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseGrid
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the manuscript grid into equal coarse cells -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem channelFineCount_eq (m B : ℕ) : channelFineCount m B = m * channelBlockCount m B := rfl

theorem channelFineCount_lower {m B : ℕ} (hm : 0 < m) :
    (5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) ≤ channelFineCount m B := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := mul_le_mul_of_nonneg_left
    (Nat.le_ceil (((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ)) / m)) hm0.le
  simpa only [channelFineCount, Nat.cast_mul, mul_div_cancel₀ _ hm0.ne'] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientLogBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Totient denominators on the major arcs -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem totient_eq_prime_product_real (q : ℕ) :
    (q.totient : ℝ) = q*∏ p ∈ q.primeFactors, (1-1/(p : ℝ)) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,
    Rat.cast_one,Rat.cast_inv,one_div] using h

/-- Only moduli up to the fixed B^15 major-arc cutoff are needed. -/
theorem totient_log_bound (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ q : ℕ,
      0 < q → q ≤ B^15 → (q : ℝ) ≤ K*Real.log B*q.totient := by
  let κ := Real.exp (-Real.eulerMascheroniConstant)/2
  have hκ : 0 < κ := half_pos (Real.exp_pos _)
  have hlim := hMP.comp ((tendsto_pow_atTop (by decide : (15 : ℕ) ≠ 0)).comp
    tendsto_natCast_atTop_atTop)
  have hsmall := hlim.eventually (eventually_ge_nhds (show κ < Real.exp (-Real.eulerMascheroniConstant) by
    dsimp [κ] <;> linarith [Real.exp_pos (-Real.eulerMascheroniConstant)]))
  refine ⟨15/κ,by positivity,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop 2] with B hproduct hB
  intro q hq hqB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hlog : 0 ≤ Real.log ((B : ℝ)^15) := Real.log_nonneg (one_le_pow₀ hB1)
  have hset : q.primeFactors ⊆ Nat.primesLE (B^15) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hqB,Nat.prime_of_mem_primeFactors hp⟩
  have hprod : (∏ p ∈ Nat.primesLE (B^15), (1-1/(p : ℝ))) ≤
      ∏ p ∈ q.primeFactors, (1-1/(p : ℝ)) := by
    apply prod_le_prod_of_subset_of_le_one hset
    · intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp1)
    · intro p _ _
      exact sub_le_self _ (by positivity)
  have hprod' : κ ≤ Real.log ((B : ℝ)^15)*
      ∏ p ∈ Nat.primesLE (B^15), (1-1/(p : ℝ)) := by
    simpa only [Function.comp_def,← Nat.cast_pow,Nat.floor_natCast,← primesLE_eq_filter] using hproduct
  have hh := hprod'.trans (mul_le_mul_of_nonneg_left hprod hlog)
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hh'' : (q : ℝ)*κ ≤ (15*Real.log B)*q.totient := by
    refine hh'.trans_eq ?_
    rw [totient_eq_prime_product_real,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  calc
    _ ≤ ((15*Real.log B)*q.totient)/κ := (le_div_iff₀ hκ).mpr hh''
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramScaleDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform decay of the histogram and residue denominator losses -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem channelMesh_scale_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    (B : ℝ)*channelMesh (channelFineCount m B) ≤ (B : ℝ)^(-(1/10 : ℝ)) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hn := channelFineCount_pos hm hB
  have hn0 : (0 : ℝ) < channelFineCount m B := by exact_mod_cast hn
  have hp := Real.rpow_pos_of_pos hB0 (11/10 : ℝ)
  have hmesh : channelMesh (channelFineCount m B) ≤ 1/(B : ℝ)^(11/10 : ℝ) := by
    unfold channelMesh
    apply (div_le_div_iff₀ hn0 hp).mpr
    simpa only [one_mul] using channelFineCount_lower (B := B) hm
  calc
    _ ≤ (B : ℝ)*(1/(B : ℝ)^(11/10 : ℝ)) := mul_le_mul_of_nonneg_left hmesh hB0.le
    _ = _ := by
      rw [mul_one_div]
      calc
        (B : ℝ)/(B : ℝ)^(11/10 : ℝ) = (B : ℝ)^(1 : ℝ)/(B : ℝ)^(11/10 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hB0]; norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramWindows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local collections of fine cells for an endpoint box -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem histogramWindowCells_length {n : ℕ} (hn : 0 < n) {l u : ℝ} (hlu : l ≤ u) :
    ((histogramWindowCells n l u).card : ℝ)*channelMesh n ≤ u-l+2*channelMesh n := by
  classical
  let J := histogramWindowCells n l u
  have hδ := channelMesh_pos hn
  by_cases hJ : J.Nonempty
  · let a := J.min' hJ
    let b := J.max' hJ
    have ha : a ∈ J := min'_mem J hJ
    have hb : b ∈ J := max'_mem J hJ
    have hab : a ≤ b := min'_le J b hb
    have hcard : J.card ≤ b.val+1-a.val := by
      have hsubset : J.image Fin.val ⊆ Icc a.val b.val := by
        intro k hk
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
        exact mem_Icc.mpr ⟨min'_le J i hi,le_max' J i hi⟩
      have hc := card_le_card hsubset
      rwa [card_image_of_injective J Fin.val_injective,Nat.card_Icc] at hc
    have hcR : (J.card : ℝ) ≤ (b.val : ℝ)+1-a.val := by
      calc
        (J.card : ℝ) ≤ ((b.val+1-a.val : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = _ := by rw [Nat.cast_sub (show a.val ≤ b.val+1 by omega),Nat.cast_add,Nat.cast_one]
    have ha' : l ≤ channelUpper n a := (mem_filter.mp ha).2.2
    have hb' : channelLower n b ≤ u := (mem_filter.mp hb).2.1
    have hlen := mul_le_mul_of_nonneg_right hcR hδ.le
    dsimp [channelLower,channelUpper] at ha' hb'
    dsimp [J] at hlen
    nlinarith
  · have he : J = ∅ := not_nonempty_iff_eq_empty.mp hJ
    change (J.card : ℝ)*channelMesh n ≤ _
    rw [he,card_empty,Nat.cast_zero,zero_mul]
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramWindowOverlap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded overlap of logarithmic windows along a geometric scale -/

namespace JointDickman
open Finset

/-- The integer lattice has at most length+1 points in any real interval. -/
theorem integer_interval_card_le (S : Finset ℤ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ m ∈ S, a ≤ (m : ℝ) ∧ (m : ℝ) ≤ b) :
    (S.card : ℝ) ≤ b-a+1 := by
  classical
  by_cases hne : S.Nonempty
  · let lo := S.min' hne
    let hi := S.max' hne
    have hlo : lo ∈ S := min'_mem S hne
    have hhi : hi ∈ S := max'_mem S hne
    have hord : lo ≤ hi := min'_le S hi hhi
    have hc : S.card ≤ (hi-lo+1).toNat := by
      have hs : S ⊆ Icc lo hi := fun m hm => mem_Icc.mpr ⟨min'_le S m hm,le_max' S m hm⟩
      have he : hi+1-lo = hi-lo+1 := by ring
      simpa only [Int.card_Icc,he] using card_le_card hs
    have hz : 0 ≤ hi-lo+1 := by omega
    have hcast : (S.card : ℝ) ≤ (hi : ℝ)-(lo : ℝ)+1 := by
      have hh : (S.card : ℤ) ≤ hi-lo+1 := by
        have hh := Int.ofNat_le.mpr hc
        simpa only [Int.toNat_of_nonneg hz] using hh
      exact_mod_cast hh
    exact hcast.trans (by linarith [(hS lo hlo).1,(hS hi hhi).2])
  · have he := not_nonempty_iff_eq_empty.mp hne
    simp only [he,card_empty,Nat.cast_zero]
    linarith

/-- For X=exp(m*t), the local cell windows have bounded overlap. The
constant depends only on their fixed width, with B*mesh displayed. -/
theorem histogramWindow_overlap {B t L U : ℝ} (hB : 0 < B) (ht : 0 < t)
    (hLU : L ≤ U) {n : ℕ} (hn : 0 < n) (S : Finset ℤ) (i : Fin n) :
    ((S.filter (fun (m : ℤ) => i ∈ histogramWindowCells n
      (((m : ℝ)*t+L)/B) (((m : ℝ)*t+U)/B))).card : ℝ) ≤
        (B*channelMesh n+U-L)/t+1 := by
  classical
  let a := (B*channelLower n i-U)/t
  let b := (B*channelUpper n i-L)/t
  have hab : a ≤ b := by
    apply (div_le_div_iff_of_pos_right ht).mpr
    have hwidth := channel_width n i
    nlinarith [channelMesh_pos hn]
  have hbnd := integer_interval_card_le
    (S.filter (fun (m : ℤ) => i ∈ histogramWindowCells n (((m : ℝ)*t+L)/B) (((m : ℝ)*t+U)/B))) hab
    (by
      intro m hm
      have hh := (mem_filter.mp (mem_filter.mp hm).2).2
      have hu := (le_div_iff₀ hB).mp hh.1
      have hl := (div_le_iff₀ hB).mp hh.2
      constructor
      · apply (div_le_iff₀ ht).mpr
        nlinarith
      · apply (le_div_iff₀ ht).mpr
        nlinarith)
  refine hbnd.trans_eq ?_
  dsimp [a,b]
  have hw := channel_width n i
  field_simp
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientSummability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The summable denominator majorant for the singular series -/

namespace JointDickman
open Filter
open scoped Topology

theorem totient_reciprocal_subpower
    (hMP : PublishedInputs.PrimeProductMertensInput) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, 1/(q.totient : ℝ) ≤ (q : ℝ)^(-1+ε) := by
  obtain ⟨K,hK,hbound⟩ := totient_log_bound hMP
  have hlim := ((log_power_div_power_tendsto_zero 1 hε).const_mul K).comp
    tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlim
  filter_upwards [hbound,hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with q hboundq hsmall hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hφ0 : (0 : ℝ) < q.totient := by
    exact_mod_cast (Nat.totient_pos.mpr (show 0 < q by omega))
  have hlogpower : K*Real.log q ≤ (q : ℝ)^ε := by
    apply (div_le_one (Real.rpow_pos_of_pos hq0 ε)).mp
    simpa only [Function.comp_def,Real.rpow_one,mul_div_assoc] using hsmall
  have hφ : 1/(q.totient : ℝ) ≤ K*Real.log q/q := by
    apply (div_le_div_iff₀ hφ0 hq0).mpr
    simpa only [one_mul] using hboundq q (by omega)
      (Nat.le_self_pow (by norm_num : 15 ≠ 0) q)
  calc
    _ ≤ K*Real.log q/q := hφ
    _ ≤ (q : ℝ)^ε/(q : ℝ) := div_le_div_of_nonneg_right hlogpower hq0.le
    _ = (q : ℝ)^ε/(q : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub hq0]; congr 1; ring

theorem summable_totient_reciprocal_sq
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    Summable (fun q : ℕ => 1/(q.totient : ℝ)^2) := by
  have hbound := totient_reciprocal_subpower hMP (by norm_num : (0 : ℝ) < 1/4)
  have hmaj : Summable (fun q : ℕ => (q : ℝ)^(-3/2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat hmaj
  filter_upwards [hbound,eventually_ge_atTop 1] with q hq hq1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(q.totient : ℝ)^2)]
  calc
    _ = (1/(q.totient : ℝ))^2 := by ring
    _ ≤ ((q : ℝ)^(-1+(1/4 : ℝ)))^2 := pow_le_pow_left₀ (by positivity) hq 2
    _ = _ := by rw [← Real.rpow_mul_natCast hq0.le]; norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The singular series produced by the Ramanujan residue factor -/

namespace JointDickman
open Finset Filter
open scoped Topology ArithmeticFunction.Moebius

theorem singularSeriesCoefficient_one (j : ℕ) : singularSeriesCoefficient j 1 = 1 := by
  simp [singularSeriesCoefficient]

theorem singularSeriesCoefficient_mul (j : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    singularSeriesCoefficient j (a*b) =
      singularSeriesCoefficient j a*singularSeriesCoefficient j b := by
  have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
  simp only [singularSeriesCoefficient,Nat.coprime_mul_iff_left,Nat.totient_mul hab,hm,
    Int.cast_mul,Nat.cast_mul]
  split_ifs <;> simp_all [div_mul_div_comm,mul_pow]

theorem singularSeriesCoefficient_norm_le (j q : ℕ) :
    ‖singularSeriesCoefficient j q‖ ≤ 1/(q.totient : ℝ)^2 := by
  unfold singularSeriesCoefficient
  split_ifs
  · rw [norm_div,Real.norm_of_nonneg (sq_nonneg _),Real.norm_eq_abs]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  · simp only [norm_zero]
    positivity

theorem singularSeriesCoefficient_summable
    (hMP : PublishedInputs.PrimeProductMertensInput) (j : ℕ) :
    Summable (fun q => ‖singularSeriesCoefficient j q‖) := by
  exact (summable_totient_reciprocal_sq hMP).of_nonneg_of_le (fun _ => norm_nonneg _)
    (singularSeriesCoefficient_norm_le j)

theorem singularSeriesCoefficient_prime_power_zero (j : ℕ) {p e : ℕ}
    (hp : p.Prime) (he : 2 ≤ e) : singularSeriesCoefficient j (p^e) = 0 := by
  have hm : μ (p^e) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (show e ≠ 0 by omega),
      ite_eq_right (show e ≠ 1 by omega)]
  simp [singularSeriesCoefficient,hm]

theorem singularSeries_local_factor (j : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, singularSeriesCoefficient j (p^e)) =
      if p ∣ j then 1 else 1-1/((p : ℝ)-1)^2 := by
  classical
  have hs : (∑' e : ℕ, singularSeriesCoefficient j (p^e)) =
      ∑ e ∈ ({0,1} : Finset ℕ), singularSeriesCoefficient j (p^e) := by
    apply tsum_eq_sum
    intro e he
    apply singularSeriesCoefficient_prime_power_zero j hp
    simp only [mem_insert,mem_singleton,not_or] at he
    omega
  rw [hs]
  simp only [sum_insert,mem_singleton,zero_ne_one,not_false_eq_true,sum_singleton,pow_zero,
    singularSeriesCoefficient_one,pow_one]
  rw [singularSeriesCoefficient,ArithmeticFunction.moebius_apply_prime hp,Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_le
  rw [Nat.cast_sub hp1]
  simp only [Nat.cast_one,Int.cast_neg,Int.cast_one,hp.coprime_iff_not_dvd]
  by_cases hd : p ∣ j <;> simp [hd,sub_eq_add_neg,neg_div]

theorem singularSeries_hasProd (hMP : PublishedInputs.PrimeProductMertensInput) (j : ℕ) :
    HasProd (fun p : Nat.Primes =>
      if (p : ℕ) ∣ j then (1 : ℝ) else 1-1/((p : ℝ)-1)^2)
      (∑' q, singularSeriesCoefficient j q) := by
  have hz : singularSeriesCoefficient j 0 = 0 := by simp [singularSeriesCoefficient]
  have h := EulerProduct.eulerProduct_hasProd (singularSeriesCoefficient_one j)
    (fun {_ _} hab => singularSeriesCoefficient_mul j hab)
    (singularSeriesCoefficient_summable hMP j) hz
  have he : (fun p : Nat.Primes => ∑' e, singularSeriesCoefficient j ((p : ℕ)^e)) =
      (fun p : Nat.Primes => if (p : ℕ) ∣ j then (1 : ℝ) else 1-1/((p : ℝ)-1)^2) := by
    funext p
    exact singularSeries_local_factor j p.property
  rwa [he] at h

theorem singularSeries_local_bounds (j : ℕ) (p : Nat.Primes) :
    0 ≤ (if (p : ℕ) ∣ j then (1 : ℝ) else 1-1/((p : ℝ)-1)^2) ∧
    (if (p : ℕ) ∣ j then (1 : ℝ) else 1-1/((p : ℝ)-1)^2) ≤ 1 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · have hs : 1 ≤ ((p : ℝ)-1)^2 := by nlinarith
    have hd : 1/((p : ℝ)-1)^2 ≤ 1 := (div_le_one (by positivity)).mpr hs
    constructor
    · linarith
    · exact sub_le_self _ (by positivity)

theorem singularSeries_bounds (hMP : PublishedInputs.PrimeProductMertensInput) (j : ℕ) :
    0 ≤ singularSeries j ∧ singularSeries j ≤ (j : ℝ)/j.totient := by
  have h := singularSeries_hasProd hMP j
  have hlo : 0 ≤ ∑' q, singularSeriesCoefficient j q :=
    h.nonneg (fun p => (singularSeries_local_bounds j p).1)
  have hhi : (∑' q, singularSeriesCoefficient j q) ≤ 1 := by
    apply le_of_tendsto' h
    intro s
    exact Finset.prod_le_one (fun p _ => (singularSeries_local_bounds j p).1)
      (fun p _ => (singularSeries_local_bounds j p).2)
  constructor
  · exact mul_nonneg (by positivity) hlo
  · simpa only [singularSeries,mul_one] using
      mul_le_mul_of_nonneg_left hhi (show 0 ≤ (j : ℝ)/j.totient by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularSeriesTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A lag-independent error for the truncated singular series -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem singularSeriesTail_nonneg (Q : ℕ) : 0 ≤ singularSeriesTail Q :=
  tsum_nonneg (fun _ => by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FineGridKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Schur bounds for the narrow logarithmic kernel on the fine grid -/

namespace JointDickman
open Finset

theorem fineGridKernel_row_bound {n : ℕ} (hn : 0 < n)
    (K : Fin n → Fin n → ℝ) {B C M : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hmesh : B*channelMesh n ≤ 1)
    (hK : ∀ i j, |K i j| ≤ M*B)
    (hsupp : ∀ i j, K i j ≠ 0 →
      |channelLower n i-channelLower n j| ≤ C/B) (i : Fin n) :
    (∑ j, channelMesh n*|K i j|) ≤ 2*M*(C+1) := by
  classical
  let J := histogramWindowCells n (channelLower n i-C/B) (channelLower n i+C/B)
  have hr : 0 ≤ C/B := div_nonneg hC hB.le
  have hlen := histogramWindowCells_length hn (show channelLower n i-C/B ≤
    channelLower n i+C/B by linarith)
  have he : (∑ j, channelMesh n*|K i j|) = ∑ j ∈ J, channelMesh n*|K i j| := by
    apply Eq.symm
    apply sum_subset (subset_univ J)
    intro j _ hj
    have hk : K i j = 0 := by
      by_contra hk
      have hb := abs_le.mp (hsupp i j hk)
      have hw := channel_width n j
      apply hj
      simp only [J,histogramWindowCells,mem_filter,mem_univ,true_and]
      constructor <;> linarith [channelMesh_pos hn]
    simp [hk]
  rw [he]
  calc
    _ ≤ ∑ _j ∈ J, channelMesh n*(M*B) :=
      sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hK i j) (channelMesh_pos hn).le)
    _ = ((J.card : ℝ)*channelMesh n)*(M*B) := by
      rw [sum_const,nsmul_eq_mul]
      ring
    _ ≤ (2*(C/B)+2*channelMesh n)*(M*B) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hM hB.le)
      exact hlen.trans_eq (by ring)
    _ = 2*M*(C+B*channelMesh n) := by field_simp
    _ ≤ 2*M*(C+1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem fineGridKernel_schur {n : ℕ} (hn : 0 < n)
    (K : Fin n → Fin n → ℝ) {B C M : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hmesh : B*channelMesh n ≤ 1)
    (hK : ∀ i j, |K i j| ≤ M*B)
    (hsupp : ∀ i j, K i j ≠ 0 →
      |channelLower n i-channelLower n j| ≤ C/B) :
    (∀ i, (∑ j, channelMesh n*|K i j|) ≤ 2*M*(C+1)) ∧
    (∀ j, (∑ i, channelMesh n*|K i j|) ≤ 2*M*(C+1)) := by
  refine ⟨fineGridKernel_row_bound hn K hB hC hM hmesh hK hsupp,?_⟩
  apply fineGridKernel_row_bound hn (fun i j => K j i) hB hC hM hmesh (fun i j => hK j i)
  intro i j hij
  simpa only [abs_sub_comm] using hsupp j i hij

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogMassBilinear
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse approximation for the actual logarithmic mass kernel -/

namespace JointDickman
open Finset Filter

theorem cellMassBilinear_reindex (m B : ℕ)
    (u v : Fin (channelFineCount m B) → ℝ)
    (U V : Fin m × Fin (channelBlockCount m B) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hu : ∀ a, u (channelIndexEquiv m B a) = channelMesh (channelFineCount m B)*U a)
    (hv : ∀ a, v (channelIndexEquiv m B a) = channelMesh (channelFineCount m B)*V a) :
    cellMassBilinear m B u v K =
      finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B))
        (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b)) U V := by
  unfold cellMassBilinear finiteKernelBilinear finiteKernelAction
  rw [← (channelIndexEquiv m B).sum_comp]
  apply sum_congr rfl
  intro a _
  rw [← (channelIndexEquiv m B).sum_comp]
  simp only [hu,hv,mul_sum]
  apply sum_congr rfl
  intro b _
  ring

theorem coarseLogMassBilinear_reindex (m B : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K =
      finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B))
        (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
        (coarseGroupAverage (groupedManuscriptChannel m B g))
        (coarseGroupAverage (groupedManuscriptChannel m B h)) := by
  apply cellMassBilinear_reindex
  · intro a
    simp only [coarseLogMass,Equiv.symm_apply_apply]
  · intro a
    simp only [coarseLogMass,Equiv.symm_apply_apply]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GeometricWindowKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The summed geometric windows form a uniformly bounded narrow kernel -/

namespace JointDickman
open Finset Filter

theorem geometricWindow_pair_distance {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U : ℝ} {k : ℤ} {i j : Fin (channelFineCount m B)}
    (hi : i ∈ geometricHistogramWindow m B t L U k)
    (hj : j ∈ geometricHistogramWindow m B t L U k) :
    |channelLower (channelFineCount m B) i-channelLower (channelFineCount m B) j| ≤
      (U-L+1)/B := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0))
  have hi' := (mem_filter.mp hi).2
  have hj' := (mem_filter.mp hj).2
  have hwi := channel_width (channelFineCount m B) i
  have hwj := channel_width (channelFineCount m B) j
  have hilo := (div_le_iff₀ hBr).mp hi'.2
  have hihi := (le_div_iff₀ hBr).mp hi'.1
  have hjlo := (div_le_iff₀ hBr).mp hj'.2
  have hjhi := (le_div_iff₀ hBr).mp hj'.1
  apply abs_le.mpr
  constructor
  · have hh : channelLower (channelFineCount m B) j-
        channelLower (channelFineCount m B) i ≤ (U-L+1)/B := by
      apply (le_div_iff₀ hBr).mpr
      nlinarith
    linarith
  · apply (le_div_iff₀ hBr).mpr
    nlinarith

theorem geometricWindowKernel_bounds {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U M : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hM : 0 ≤ M)
    (S : Finset ℤ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, |V k i j| ≤ M) :
    (∀ i j, |geometricWindowKernel m B t L U S V i j| ≤ (((1+U-L)/t+1)*M)*B) ∧
    (∀ i j, geometricWindowKernel m B t L U S V i j ≠ 0 →
      |channelLower (channelFineCount m B) i-channelLower (channelFineCount m B) j| ≤
        (U-L+1)/B) := by
  classical
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0))
  constructor
  · intro i j
    let A := S.filter (fun k => i ∈ geometricHistogramWindow m B t L U k)
    have hcard : (A.card : ℝ) ≤ (1+U-L)/t+1 :=
      (histogramWindow_overlap hBr ht hLU (channelFineCount_pos hm hBpos) S i).trans
        (by gcongr)
    have hterm (k : ℤ) (hk : k ∈ S) :
        |(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then V k i j else 0)| ≤
          if i ∈ geometricHistogramWindow m B t L U k then M else 0 := by
      by_cases hi : i ∈ geometricHistogramWindow m B t L U k
      · by_cases hj : j ∈ geometricHistogramWindow m B t L U k
        · simpa only [hi,hj,and_self,ite_true, if_true] using hV k hk i j
        · simpa [hi,hj] using hM
      · simp [hi]
    unfold geometricWindowKernel
    rw [abs_mul,abs_of_pos hBr]
    calc
      _ ≤ (B : ℝ)*∑ k ∈ S, |(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then V k i j else 0)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hBr.le
      _ ≤ (B : ℝ)*∑ k ∈ S, if i ∈ geometricHistogramWindow m B t L U k then M else 0 :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) hBr.le
      _ = (B : ℝ)*((A.card : ℝ)*M) := by rw [← sum_filter,sum_const,nsmul_eq_mul]
      _ ≤ (B : ℝ)*(((1+U-L)/t+1)*M) := by gcongr
      _ = _ := by ring
  · intro i j hne
    have hs : (∑ k ∈ S, if i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k then V k i j else 0) ≠ 0 := by
      intro hs
      exact hne (by simp [geometricWindowKernel,hs])
    obtain ⟨k,_hk,hkv⟩ := exists_ne_zero_of_sum_ne_zero hs
    have hij : i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k := by
      by_contra h
      exact hkv (ite_eq_right h)
    exact geometricWindow_pair_distance hm hB hij.1 hij.2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GeometricCoarseKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse comparison for the actual box-summed spatial kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem endpointSpatialWeight_bound (m B : ℕ) (t β : ℝ) (S : Finset ℤ)
    (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {D M₁ M₂ M : ℝ}
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hd : ∀ k ∈ S, |d k| ≤ D) (hw₁ : ∀ x, |w₁ x| ≤ M₁)
    (hw₂ : ∀ x, |w₂ x| ≤ M₂) (hw : ∀ x, |w x| ≤ M) :
    ∀ k ∈ S, ∀ i j, |endpointSpatialWeight m B t β d w₁ w₂ w k i j| ≤ D*M₁*M₂*M := by
  intro k hk i j
  unfold endpointSpatialWeight
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul (hd k hk) (hw₁ _) (abs_nonneg _) hD)
    (hw₂ _) (abs_nonneg _) (mul_nonneg hD hM₁)) (hw _) (abs_nonneg _)
      (mul_nonneg (mul_nonneg hD hM₁) hM₂)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedArithmeticIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact arithmetic meaning of the geometric-box period integral -/

namespace JointDickman
open Finset MeasureTheory

theorem weightedGeometricPeriodSum_eq_arithmeticSum (B j : ℕ) {a b l u T t : ℝ}
    (hT : 0 < T) (hl : 0 < l) (hlu : l ≤ u)
    (S : Finset ℤ) (r : ℤ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w =
      (weightedGeometricArithmeticSum B j a b l u T t S r g h w₁ w₂ w : ℂ) := by
  classical
  have hcoeff (X : ℝ) (hX : 0 < X) (θ : ℝ) :
      smoothCoefficientAdditiveSum B X θ w =
        finiteAdditiveSum (Ioc ⌊l*X⌋₊ ⌊u*X⌋₊)
          (fun c => (coefficientWeight B c*w (c/X) : ℝ)) θ := by
    unfold smoothCoefficientAdditiveSum finiteAdditiveSum
    rw [tsum_eq_Ioc_of_scaled_support hl.le hlu hX hsupp _
      (by intro n hn; simp [hn])]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  unfold weightedGeometricPeriodSum weightedGeometricArithmeticSum
  push_cast
  congr 1
  apply sum_congr rfl
  intro k _
  congr 1
  have hX : 0 < Real.exp ((k : ℝ)*t)/T := div_pos (Real.exp_pos _) hT
  simp only [geometricBoxIntegrand,endpointFourierSum]
  simp_rw [hcoeff _ hX]
  rw [finiteKernel_orthogonality]
  simp only [apply_ite,Complex.ofReal_mul,Complex.ofReal_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularTailRate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A power bound for the singular-series tail at the manuscript cutoff -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem summable_weighted_totient_reciprocal_sq
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    Summable (fun q : ℕ => (q : ℝ)^(1/4 : ℝ)/(q.totient : ℝ)^2) := by
  have hbound := totient_reciprocal_subpower hMP (by norm_num : (0 : ℝ) < 1/8)
  have hmaj : Summable (fun q : ℕ => (q : ℝ)^(-(3/2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat hmaj
  filter_upwards [hbound,eventually_ge_atTop 1] with q hq hq1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (q : ℝ)^(1/4 : ℝ)/(q.totient : ℝ)^2)]
  calc
    _ = (q : ℝ)^(1/4 : ℝ)*(1/(q.totient : ℝ))^2 := by ring
    _ ≤ (q : ℝ)^(1/4 : ℝ)*((q : ℝ)^(-1+(1/8 : ℝ)))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq 2) (by positivity)
    _ = _ := by rw [← Real.rpow_mul_natCast hq0.le,← Real.rpow_add hq0]; norm_num

theorem singularSeriesTail_power_bound
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ Q : ℕ, 0 < Q →
      singularSeriesTail Q ≤ A*(Q : ℝ)^(-(1/4 : ℝ)) := by
  let f := fun q : ℕ => (q : ℝ)^(1/4 : ℝ)/(q.totient : ℝ)^2
  have hf : Summable f := summable_weighted_totient_reciprocal_sq hMP
  refine ⟨∑' q, f q,tsum_nonneg (fun _ => by dsimp [f] <;> positivity),?_⟩
  intro Q hQ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have htail : Summable (fun k : ℕ => 1/((k+Q).totient : ℝ)^2) :=
    (summable_totient_reciprocal_sq hMP).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hftail : Summable (fun k : ℕ => f (k+Q)) :=
    hf.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hmul : (Q : ℝ)^(1/4 : ℝ)*singularSeriesTail Q ≤ ∑' q, f q := by
    calc
      _ = ∑' k : ℕ, (Q : ℝ)^(1/4 : ℝ)*(1/((k+Q).totient : ℝ)^2) := by
        rw [tsum_mul_left]; rfl
      _ ≤ ∑' k : ℕ, f (k+Q) := by
        apply (htail.mul_left _).tsum_le_tsum _ hftail
        intro k
        dsimp [f]
        rw [div_eq_mul_inv,one_div]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow hQr.le (by exact_mod_cast (Nat.le_add_left Q k)) (by norm_num)
      _ ≤ ∑' q, f q := by
        have he := hf.sum_add_tsum_nat_add Q
        have hp : 0 ≤ ∑ q ∈ range Q, f q := sum_nonneg (fun _ _ => by dsimp [f] <;> positivity)
        linarith
  have hdiv : singularSeriesTail Q ≤ (∑' q, f q) / (Q : ℝ)^(1/4 : ℝ) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hQr (1/4 : ℝ))).mpr
      ((_root_.mul_comm _ _).trans_le hmul)
  simpa only [Real.rpow_neg hQr.le,div_eq_mul_inv] using hdiv

theorem singularSeriesTail_uniform_vanishing
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j Q : ℕ, 0 < j → j ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ((j : ℝ)/j.totient)*singularSeriesTail (Q+1) ≤ ε B := by
  obtain ⟨A,hA,hpower⟩ := singularSeriesTail_power_bound hMP
  obtain ⟨K,hK,htotient⟩ := totient_log_bound hMP
  refine ⟨fun B => K*A*(Real.log B/(B : ℝ)^(1/10 : ℝ)),?_,?_⟩
  · have hlim := ((log_power_div_power_tendsto_zero 1 (by norm_num : (0 : ℝ) < 1/10)).const_mul
      (K*A)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def,Real.rpow_one,mul_zero] using hlim
  filter_upwards [htotient,eventually_ge_atTop 1] with B htot hB
  intro j Q hj hjB hQ
  have hBr : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hφ : (0 : ℝ) < j.totient := by exact_mod_cast Nat.totient_pos.mpr hj
  have hjpow : j ≤ B^15 := hjB.trans (le_self_pow₀ hB (by decide : 15 ≠ 0))
  have hratio : (j : ℝ)/j.totient ≤ K*Real.log B :=
    (div_le_iff₀ hφ).mpr (htot j hj hjpow)
  have hQ' : (B : ℝ)^(2/5 : ℝ) ≤ (Q+1 : ℕ) :=
    hQ.trans (by exact_mod_cast Nat.le_succ Q)
  have hdecay : ((Q+1 : ℕ) : ℝ)^(-(1/4 : ℝ)) ≤ (B : ℝ)^(-(1/10 : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hBr (2/5 : ℝ)) hQ'
      (by norm_num : -(1/4 : ℝ) ≤ 0)
    rw [← Real.rpow_mul hBr.le] at hh
    norm_num at hh ⊢
    exact hh
  calc
    _ ≤ (K*Real.log B)*(A*((Q+1 : ℕ) : ℝ)^(-(1/4 : ℝ))) :=
      mul_le_mul hratio (hpower (Q+1) (by omega)) (singularSeriesTail_nonneg _)
        (mul_nonneg hK.le (Real.log_nonneg hB1))
    _ ≤ (K*Real.log B)*(A*(B : ℝ)^(-(1/10 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdecay hA)
        (mul_nonneg hK.le (Real.log_nonneg hB1))
    _ = _ := by rw [Real.rpow_neg hBr.le]; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPeriodCoarse
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the original Fourier expression to the coarse spatial kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem weighted_geometric_period_coarse_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ)
    {M D₁ D₂ M₀ D₀ R : ℝ} (hR : 0 ≤ R) (hMb : 0 ≤ M) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M) (hwb₂ : ∀ x, |w₂ x| ≤ M)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) (fun k => r k*d k) w₁ w₂ w)
      T*‖weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*
          (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K : ℂ)‖ ≤
        ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1)+δ*(T/j)*singularSeries j := by
  obtain ⟨c,hc,hcpos,H,ε₁,hε₁,hperiod⟩ := weighted_geometric_period_model_vanishing_jd
    hSD hSW hM hMP ha hab hl hlu ht hη w₁ w₂ w w' hR hMb hM₀ hD₀
    hwb₁ hwb₂ hw hw' hwb hwd hsupp
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨C,hC,ε₂,hε₂,hcoarse⟩ := bounded_box_coarse_comparison_jd hSD hSW hM hMP
    (mul_nonneg hR hD) ha hab ht hη w₁ w₂ w₁' w₂' w hMb hMb hD₁ hD₂ hM₀
    hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hwb hs₁ hs₂
  refine ⟨c,hc,hcpos,H,C,hC,fun B => ε₁ B+ε₂ B,by simpa using hε₁.add hε₂,?_⟩
  intro δ hδ
  obtain ⟨m,hm,hcoarseB⟩ := hcoarse δ hδ
  refine ⟨m,hm,?_⟩
  filter_upwards [hperiod,hcoarseB,hden,eventually_ge_atTop 1] with B hp hcB hd hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog r hr g h hg hh
  dsimp only
  have hjB : j ≤ B := (Nat.le_mul_of_pos_right j hQ).trans hscale
  have hscale' : η*T ≤ (B : ℝ) := hlag.trans (by exact_mod_cast hjB)
  have hp' := hp T hT hscale' S hbox hlog r hr j Q hcut g h hg hh
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hrd : ∀ k ∈ S, |r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ R*D := by
    intro k hk
    rw [abs_mul]
    apply mul_le_mul (hr k hk) _ (abs_nonneg _) hR
    apply hd.1
    apply (le_div_iff₀ hBpos).mpr
    nlinarith [(hlog k hk).1]
  have hc' := hcB j Q hQ hscale T hT hlag S hbox
    (fun k => r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)) hrd g h hg hh
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w)
    (geometricFullArcSum B j Q a b T t S
      (fun k => r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
      g h w₁ w₂ w)
    (((singularSeries j : ℂ)/j)*
      (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h)
        (geometricWindowKernel m B t (Real.log a) (Real.log b) S
          (endpointSpatialWeight m B t (T/j)
            (fun k => r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
            w₁ w₂ w)) : ℂ))
  have he := (mul_le_mul_of_nonneg_left htri hT.le).trans_eq (mul_add _ _ _)
  exact (he.trans (add_le_add hp' hc')).trans_eq (by ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPeriodVanishing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform vanishing of the retained-denominator tail -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem weighted_geometric_period_coarse_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ)
    {M D₁ D₂ M₀ D₀ R : ℝ} (hR : 0 ≤ R) (hMb : 0 ≤ M) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M) (hwb₂ : ∀ x, |w₂ x| ≤ M)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) (fun k => r k*d k) w₁ w₂ w)
      T*‖weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*
          (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K : ℂ)‖ ≤
        ε B+δ*(T/j)*singularSeries j := by
  obtain ⟨c,hc,hcpos,H,C,hC,ε₁,hε₁,hcompare⟩ := weighted_geometric_period_coarse_comparison
    hSD hSW hM hMP ha hab hl hlu ht hη w₁ w₂ w₁' w₂' w w'
    hR hMb hD₁ hD₂ hM₀ hD₀ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hs₁ hs₂ hw hw' hwb hwd hsupp
  obtain ⟨ε₂,hε₂,htail⟩ := singularSeriesTail_uniform_vanishing hMP
  refine ⟨c,hc,hcpos,H,fun B => ε₁ B+(C/η)*ε₂ B,?_,?_⟩
  · simpa using hε₁.add (hε₂.const_mul (C/η))
  intro δ hδ
  obtain ⟨m,hm,hcompareB⟩ := hcompare δ hδ
  refine ⟨m,hm,?_⟩
  filter_upwards [hcompareB,htail] with B hcB htB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog r hr g h hg hh
  dsimp only
  have hj : 0 < j := Nat.pos_of_ne_zero (NeZero.ne j)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hjB : j ≤ B := (Nat.le_mul_of_pos_right j hQ).trans hscale
  have hratio : T/(j : ℝ) ≤ 1/η := by
    apply (div_le_div_iff₀ hjr hη).mpr
    simpa only [one_mul,mul_one,mul_comm] using hlag
  have ht' := htB j Q hj hjB hcut
  have hpos : 0 ≤ ((j : ℝ)/j.totient)*singularSeriesTail (Q+1) :=
    mul_nonneg (by positivity) (singularSeriesTail_nonneg _)
  have herror : C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1) ≤ (C/η)*ε₂ B := by
    calc
      _ = C*(T/j)*(((j : ℝ)/j.totient)*singularSeriesTail (Q+1)) := by ring
      _ ≤ C*(1/η)*(((j : ℝ)/j.totient)*singularSeriesTail (Q+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) hpos
      _ ≤ C*(1/η)*ε₂ B := mul_le_mul_of_nonneg_left ht' (by positivity)
      _ = _ := by ring
  have hfinal := hcB j Q hQ hscale hcut T hT hlag S hbox hlog r hr g h hg hh
  dsimp only at hfinal
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeCoarseFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded coarse features of the actual prime-site distribution -/

namespace JointDickman
open Finset

theorem channelBlockCount_pos {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    0 < channelBlockCount m B := by
  have h := channelFineCount_pos hm hB
  rw [channelFineCount_eq] at h
  exact Nat.pos_of_ne_zero (by intro he; simp [he] at h)

theorem channelMesh_block_normalization {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    channelMesh (channelFineCount m B)*(channelBlockCount m B : ℝ) = channelMesh m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk0 : (channelBlockCount m B : ℝ) ≠ 0 := by
    exact_mod_cast (channelBlockCount_pos hm hB).ne'
  unfold channelMesh
  rw [channelFineCount_eq,Nat.cast_mul]
  field_simp

theorem primeCoarseFeature_bounds {m B : ℕ} (hm : 0 < m)
    (d : Fin m) (x : auxiliaryPrimes B → Bool) :
    0 ≤ primeCoarseFeature m B d x ∧ primeCoarseFeature m B d x ≤ 1/channelMesh m := by
  have hp (a : Fin m × Fin (channelBlockCount m B)) :
      0 ≤ primeGroupedTransition m B x a := partialFairPrimeTransition_nonneg _ _ _ _
  have hsum : (∑ r, primeGroupedTransition m B x (d,r)) ≤ 1 := by
    have hh := single_le_sum (s := univ) (f := fun e : Fin m =>
      ∑ r, primeGroupedTransition m B x (e,r))
      (fun e _ => sum_nonneg (fun r _ => hp (e,r))) (mem_univ d)
    have htotal : (∑ e : Fin m, ∑ r, primeGroupedTransition m B x (e,r)) ≤ 1 := by
      rw [← Fintype.sum_prod_type]
      exact partialFairPrimeTransition_sum_le _ _ _
    exact hh.trans htotal
  unfold primeCoarseFeature
  exact ⟨div_nonneg (sum_nonneg (fun r _ => hp (d,r))) (channelMesh_pos hm).le,
    div_le_div_of_nonneg_right hsum (channelMesh_pos hm).le⟩

theorem groupedManuscriptChannel_coarse_feature {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (a : Fin m × Fin (channelBlockCount m B)) :
    coarseGroupAverage (groupedManuscriptChannel m B g) a =
      ∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*primeCoarseFeature m B a.1 x := by
  have hm0 := (channelMesh_pos hm).ne'
  have hδ0 := (channelMesh_pos (channelFineCount_pos hm hB)).ne'
  have hk0 : (channelBlockCount m B : ℝ) ≠ 0 := by
    exact_mod_cast (channelBlockCount_pos hm hB).ne'
  have he := channelMesh_block_normalization hm hB
  unfold coarseGroupAverage finiteResidueAverage groupedManuscriptChannel finiteChannel primeCoarseFeature
  simp only [Fintype.card_fin]
  change ((∑ r : Fin (channelBlockCount m B),
      (∑ x, fullPrimeMass (auxiliaryPrimes B) x*primeGroupedTransition m B x (a.1,r)*g x)/
        channelMesh (channelFineCount m B))/(channelBlockCount m B : ℝ)) = _
  simp only [sum_div,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro r _
  rw [← he]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GroupedKernelFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-feature form of a coarse kernel -/

namespace JointDickman
open Finset

theorem groupedKernelBilinear_eq {D R : Type*} [Fintype D] [Fintype R]
    (δ : ℝ) (K : D × R → D × R → ℝ) (u v : D → ℝ) :
    finiteKernelBilinear (fun _ => δ) K (fun a => u a.1) (fun a => v a.1) =
      ∑ d, ∑ e, groupedKernelCoefficient δ K d e*u d*v e := by
  simp only [finiteKernelBilinear,finiteKernelAction,Fintype.sum_prod_type,
    groupedKernelCoefficient,mul_sum,sum_mul]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  ring

theorem coarseLogMassBilinear_features {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K =
      ∑ d, ∑ e, primeCoarseCoefficient m B K d e*
        (∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*primeCoarseFeature m B d x)*
        (∑ y, fullPrimeMass (auxiliaryPrimes B) y*h y*primeCoarseFeature m B e y) := by
  rw [coarseLogMassBilinear_reindex]
  rw [funext (fun a => groupedManuscriptChannel_coarse_feature hm hB g a),
    funext (fun a => groupedManuscriptChannel_coarse_feature hm hB h a)]
  exact groupedKernelBilinear_eq (D := Fin m) (R := Fin (channelBlockCount m B))
    (channelMesh (channelFineCount m B))
    (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
    (fun d => ∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*primeCoarseFeature m B d x)
    (fun e => ∑ y, fullPrimeMass (auxiliaryPrimes B) y*h y*primeCoarseFeature m B e y)

theorem sum_four_comm {X Y D E : Type*} [Fintype X] [Fintype Y] [Fintype D] [Fintype E]
    (f : X → Y → D → E → ℝ) :
    (∑ x, ∑ y, ∑ d, ∑ e, f x y d e) = ∑ d, ∑ e, ∑ x, ∑ y, f x y d e := by
  calc
    _ = ∑ x, ∑ d, ∑ y, ∑ e, f x y d e := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = ∑ d, ∑ x, ∑ y, ∑ e, f x y d e := sum_comm
    _ = ∑ d, ∑ x, ∑ e, ∑ y, f x y d e := by
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d _
      rw [sum_comm]

theorem primeCoarseKernel_test (m B : ℕ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    (∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
      g x*h y*primeCoarseKernel m B K x y) =
      ∑ d, ∑ e, primeCoarseCoefficient m B K d e*
        (∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*primeCoarseFeature m B d x)*
        (∑ y, fullPrimeMass (auxiliaryPrimes B) y*h y*primeCoarseFeature m B e y) := by
  simp only [primeCoarseKernel,mul_sum,sum_mul]
  rw [sum_four_comm]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

theorem coarseLogMassBilinear_eq_kernel_test {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K =
      ∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
        g x*h y*primeCoarseKernel m B K x y := by
  rw [coarseLogMassBilinear_features hm hB,primeCoarseKernel_test]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedArithmeticFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated arithmetic kernel has a finite-feature approximation -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem weighted_geometric_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ)
    {M D₁ D₂ M₀ D₀ R : ℝ} (hR : 0 ≤ R) (hMb : 0 ≤ M) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M) (hwb₂ : ∀ x, |w₂ x| ≤ M)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) (fun k => r k*d k) w₁ w₂ w)
      T*|weightedGeometricArithmeticSum B j a b l u T t S r g h w₁ w₂ w-
        (singularSeries j/(j : ℝ))*
          (∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*primeCoarseKernel m B K x y)| ≤
        ε B+δ*(T/j)*singularSeries j := by
  obtain ⟨c,hc,hcpos,H,ε,hε,hcompare⟩ := weighted_geometric_period_coarse_vanishing
    hSD hSW hM hMP ha hab hl hlu ht hη w₁ w₂ w₁' w₂' w w'
    hR hMb hD₁ hD₂ hM₀ hD₀ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hs₁ hs₂ hw hw' hwb hwd hsupp
  refine ⟨c,hc,hcpos,H,ε,hε,?_⟩
  intro δ hδ
  obtain ⟨m,hm,hcompareB⟩ := hcompare δ hδ
  refine ⟨m,hm,?_⟩
  filter_upwards [hcompareB,eventually_gt_atTop 0] with B hcB hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog r hr g h hg hh
  dsimp only
  have he := hcB j Q hQ hscale hcut T hT hlag S hbox hlog r hr g h hg hh
  dsimp only at he
  rw [weightedGeometricPeriodSum_eq_arithmeticSum B j hT hl hlu S r g h w₁ w₂ w hsupp,
    coarseLogMassBilinear_eq_kernel_test hm hB] at he
  simpa only [← Complex.ofReal_natCast,← Complex.ofReal_div,← Complex.ofReal_mul,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CompactTensorApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite tensor approximation on the four-variable smooth support -/

namespace JointDickman
open scoped Topology

theorem supportPolynomialMap_apply (K : Set (Fin 4 → ℝ))
    (P : MvPolynomial (Fin 4) ℝ) (x : K) :
    supportPolynomialMap K P x = MvPolynomial.eval (x : Fin 4 → ℝ) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [supportPolynomialMap]
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p i hp =>
    have hp' := hp
    unfold supportPolynomialMap at hp'
    simp [supportPolynomialMap,map_mul,hp']

theorem supportPolynomialMap_separates (K : Set (Fin 4 → ℝ)) :
    (supportPolynomialMap K).range.SeparatesPoints := by
  intro x y hxy
  have hne : (x : Fin 4 → ℝ) ≠ (y : Fin 4 → ℝ) := fun he => hxy (Subtype.ext he)
  have hex : ∃ i : Fin 4, (x : Fin 4 → ℝ) i ≠ (y : Fin 4 → ℝ) i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i,hi⟩ := hex
  refine ⟨fun x => supportPolynomialMap K (MvPolynomial.X i) x,
    ⟨supportPolynomialMap K (MvPolynomial.X i),
      (supportPolynomialMap K).mem_range_self (MvPolynomial.X i),rfl⟩,?_⟩
  simpa only [supportPolynomialMap_apply,MvPolynomial.eval_X] using hi

/-- The fourth coordinate can carry the external smooth parameter. Each
polynomial is a finite sum of products of one-coordinate powers. -/
theorem compact_support_polynomial_approximation (K : Set (Fin 4 → ℝ))
    (hK : IsCompact K) (f : C(K,ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 4) ℝ, ∀ x : K,
      |MvPolynomial.eval (x : Fin 4 → ℝ) P-f x| < ε := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨g,hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (supportPolynomialMap K).range (supportPolynomialMap_separates K) f f.continuous ε hε
  obtain ⟨P,hP⟩ := g.property
  refine ⟨P,?_⟩
  intro x
  have hh := hg x
  rw [← hP] at hh
  change ‖supportPolynomialMap K P x-f x‖ < ε at hh
  simpa only [supportPolynomialMap_apply,Real.norm_eq_abs] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TensorCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth separated factors for compact polynomial approximation -/

namespace JointDickman
open Finset
open scoped SchwartzMap

theorem tensorBoxBump_one {x : ℝ} (hx : x ∈ Set.Icc (1/2) 4) : tensorBoxBump x = 1 := by
  apply tensorBoxBump.one_of_mem_closedBall
  change dist x (9/4 : ℝ) ≤ (7/4 : ℝ)
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [hx.1,hx.2]

theorem tensorBoxBump_zero {x : ℝ} (hx : x ≤ 1/4 ∨ 17/4 < x) : tensorBoxBump x = 0 := by
  apply tensorBoxBump.zero_of_le_dist
  change (2 : ℝ) ≤ dist x (9/4 : ℝ)
  rw [Real.dist_eq]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem tensorPowerFactor_apply (n : ℕ) (x : ℝ) :
    tensorPowerFactor n x = x^n*tensorBoxBump x := rfl

theorem tensorPowerFactor_support (n : ℕ) (x : ℝ) (hx : x ≤ 1/4 ∨ 17/4 < x) :
    tensorPowerFactor n x = 0 := by rw [tensorPowerFactor_apply,tensorBoxBump_zero hx,mul_zero]

theorem schwartz_value_derivative_bounds (w : 𝓢(ℝ,ℝ)) :
    ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧ (∀ x, |w x| ≤ M) ∧
      (∀ x, |deriv w x| ≤ D) ∧ Continuous (deriv w) := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 w,
    SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ w),
    apply_nonneg _ _,apply_nonneg _ _,?_,?_,?_⟩
  · intro x
    simpa only [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ w x
  · intro x
    simpa only [Real.norm_eq_abs,SchwartzMap.derivCLM_apply] using
      SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.derivCLM ℝ ℝ w) x
  · exact (SchwartzMap.derivCLM ℝ ℝ w).continuous

theorem tensor_polynomial_expansion (P : MvPolynomial (Fin 4) ℝ) (x y z s : ℝ) :
    MvPolynomial.eval ![x,y,z,s] P*tensorBoxBump x*tensorBoxBump y*tensorBoxBump z =
      ∑ d ∈ P.support, (P.coeff d*s^(d 3))*
        tensorPowerFactor (d 0) x*tensorPowerFactor (d 1) y*tensorPowerFactor (d 2) z := by
  rw [MvPolynomial.eval_eq']
  simp only [sum_mul]
  apply sum_congr rfl
  intro d _
  simp only [tensorPowerFactor_apply]
  simp [Fin.prod_univ_succ]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SchwartzArithmeticFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted arithmetic comparison for compact Schwartz factors -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem schwartz_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η) (hR : 0 ≤ R)
    (w₁ w₂ w : 𝓢(ℝ,ℝ))
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hs₃ : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
      T*|weightedGeometricArithmeticSum B j a b l u T t S r g h w₁ w₂ w-
        (singularSeries j/(j : ℝ))*
          (∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*primeCoarseKernel m B K x y)| ≤
        ε B+δ*(T/j)*singularSeries j := by
  obtain ⟨M₁,D₁,hM₁,hD₁,hv₁,hd₁,_⟩ := schwartz_value_derivative_bounds w₁
  obtain ⟨M₂,D₂,hM₂,hD₂,hv₂,hd₂,_⟩ := schwartz_value_derivative_bounds w₂
  obtain ⟨M₀,D₀,hM₀,hD₀,hv₀,hd₀,hc₀⟩ := schwartz_value_derivative_bounds w
  exact weighted_geometric_arithmetic_feature_comparison hSD hSW hM hMP
    ha hab hl hlu ht hη w₁ w₂ (deriv w₁) (deriv w₂) w (deriv w) hR
    (add_nonneg hM₁ hM₂) hD₁ hD₂ hM₀ hD₀ w₁.hasDerivAt w₂.hasDerivAt
    (fun x => (hv₁ x).trans (le_add_of_nonneg_right hM₂))
    (fun x => (hv₂ x).trans (le_add_of_nonneg_left hM₁)) hd₁ hd₂ hs₁ hs₂
    w.hasDerivAt hc₀ hv₀ hd₀ hs₃

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseFeatureBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the finite-feature approximation -/

namespace JointDickman
open Finset

theorem groupedKernelCoefficient_bound {D R : Type*} [Fintype D] [Fintype R]
    (δ : ℝ) (K : D × R → D × R → ℝ) {C : ℝ} (hδ : 0 ≤ δ)
    (hrow : ∀ a, (∑ b, δ*|K a b|) ≤ C) (d e : D) :
    |groupedKernelCoefficient δ K d e| ≤ δ*(Fintype.card R : ℝ)*C := by
  have hpart (r : R) : (∑ s, δ*|K (d,r) (e,s)|) ≤ C := by
    have hh := single_le_sum (s := univ) (f := fun b : D => ∑ s, δ*|K (d,r) (b,s)|)
      (fun b _ => sum_nonneg (fun s _ => mul_nonneg hδ (abs_nonneg _))) (mem_univ e)
    exact hh.trans (by simpa only [Fintype.sum_prod_type] using hrow (d,r))
  calc
    _ = δ^2*|∑ r, ∑ s, K (d,r) (e,s)| := by
      rw [groupedKernelCoefficient,abs_mul,abs_of_nonneg (sq_nonneg δ)]
    _ ≤ δ^2*(∑ r, ∑ s, |K (d,r) (e,s)|) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun r _ => abs_sum_le_sum_abs _ _))
    _ = δ*(∑ r, ∑ s, δ*|K (d,r) (e,s)|) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      ring
    _ ≤ δ*(∑ _r : R, C) := mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hpart r)) hδ
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul] <;> ring

theorem primeCoarseCoefficient_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    {C : ℝ} (hrow : ∀ i, (∑ j, channelMesh (channelFineCount m B)*|K i j|) ≤ C)
    (d e : Fin m) : |primeCoarseCoefficient m B K d e| ≤ channelMesh m*C := by
  have hr (a : Fin m × Fin (channelBlockCount m B)) :
      (∑ b, channelMesh (channelFineCount m B)*
        |K (channelIndexEquiv m B a) (channelIndexEquiv m B b)|) ≤ C := by
    rw [(channelIndexEquiv m B).sum_comp
      (fun j => channelMesh (channelFineCount m B)*|K (channelIndexEquiv m B a) j|)]
    exact hrow _
  have hh := groupedKernelCoefficient_bound (channelMesh (channelFineCount m B))
    (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
    (channelMesh_pos (channelFineCount_pos hm hB)).le hr d e
  simpa only [primeCoarseCoefficient,Fintype.card_fin,channelMesh_block_normalization hm hB] using hh

theorem primeCoarseKernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, channelMesh (channelFineCount m B)*|K i j|) ≤ C)
    (x y : auxiliaryPrimes B → Bool) :
    |primeCoarseKernel m B K x y| ≤ (m : ℝ)^2*C/channelMesh m := by
  have hμ := channelMesh_pos hm
  have hterm (d e : Fin m) :
      |primeCoarseCoefficient m B K d e*primeCoarseFeature m B d x*primeCoarseFeature m B e y| ≤
        C/channelMesh m := by
    rw [abs_mul,abs_mul,
      abs_of_nonneg (primeCoarseFeature_bounds hm d x).1,
      abs_of_nonneg (primeCoarseFeature_bounds hm e y).1]
    have hh := mul_le_mul
      (mul_le_mul (primeCoarseCoefficient_bound hm hB K hrow d e)
        (primeCoarseFeature_bounds hm d x).2 (primeCoarseFeature_bounds hm d x).1
        (mul_nonneg hμ.le hC))
      (primeCoarseFeature_bounds hm e y).2 (primeCoarseFeature_bounds hm e y).1
      (by positivity : 0 ≤ channelMesh m*C*(1/channelMesh m))
    exact hh.trans_eq (by field_simp)
  unfold primeCoarseKernel
  calc
    _ ≤ ∑ d : Fin m, ∑ e : Fin m,
        |primeCoarseCoefficient m B K d e*primeCoarseFeature m B d x*primeCoarseFeature m B e y| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun d _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _d : Fin m, ∑ _e : Fin m, C/channelMesh m :=
      sum_le_sum (fun d _ => sum_le_sum (fun e _ => hterm d e))
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricFeatureBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual box-summed finite-feature kernel -/

namespace JointDickman
open Finset

theorem geometric_primeCoarseKernel_bound {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t β a b D M₁ M₂ M₀ : ℝ} (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₀ : 0 ≤ M₀)
    (S : Finset ℤ) (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hd : ∀ k ∈ S, |d k| ≤ D)
    (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀)
    (x y : auxiliaryPrimes B → Bool) :
    |primeCoarseKernel m B
      (geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t β d w₁ w₂ w)) x y| ≤
      (m : ℝ)^2*(2*((((1+Real.log b-Real.log a)/t+1)*(D*M₁*M₂*M₀)))*
        (Real.log b-Real.log a+2))/channelMesh m := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hlogs := Real.log_le_log ha hab
  let M := ((1+Real.log b-Real.log a)/t+1)*(D*M₁*M₂*M₀)
  have hoverlap : 0 ≤ (1+Real.log b-Real.log a)/t+1 :=
    add_nonneg (div_nonneg (by linarith) ht.le) zero_le_one
  have hM : 0 ≤ M := mul_nonneg hoverlap (by positivity)
  have hwidth : 0 ≤ Real.log b-Real.log a+1 := by linarith
  have hwidth' : 0 ≤ Real.log b-Real.log a+2 := by linarith
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : -(1/10 : ℝ) ≤ 0))
  obtain ⟨hheight,hsupp⟩ := geometricWindowKernel_bounds hm hB ht hlogs
    (by positivity : 0 ≤ D*M₁*M₂*M₀) S (endpointSpatialWeight m B t β d w₁ w₂ w)
    (endpointSpatialWeight_bound m B t β S d w₁ w₂ w hD hM₁ hM₂ hd hw₁ hw₂ hw)
  have hr := (fineGridKernel_schur (channelFineCount_pos hm hBpos) _ hBr hwidth hM hmesh hheight hsupp).1
  have hh := primeCoarseKernel_bound hm hBpos
    (geometricWindowKernel m B t (Real.log a) (Real.log b) S
      (endpointSpatialWeight m B t β d w₁ w₂ w)) (by positivity : 0 ≤ 2*M*(Real.log b-Real.log a+2))
    (by intro i; convert hr i using 1; ring) x y
  simpa only [M,sub_add_eq_add_sub,add_assoc] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeKernelMeanBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded prime-site kernel has a bounded independent mean -/

namespace JointDickman
open Finset

theorem fullPrimeMass_total (P : Finset ℕ) : (∑ x, fullPrimeMass P x) = 1 :=
  bernoulliSiteMass_sum _

theorem primeKernel_mean_abs_le (B : ℕ)
    (K : (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ)
    {C : ℝ} (hK : ∀ x y, |K x y| ≤ C) :
    |∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*K x y| ≤ C := by
  let μ := fullPrimeMass (auxiliaryPrimes B)
  have hμ : ∀ x, 0 ≤ μ x := fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B)
  calc
    _ ≤ ∑ x, ∑ y, μ x*μ y*|K x y| := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro x _
      exact (abs_sum_le_sum_abs _ _).trans_eq (by
        apply sum_congr rfl
        intro y _
        rw [abs_mul,abs_of_nonneg (mul_nonneg (hμ x) (hμ y))])
    _ ≤ ∑ x, ∑ y, μ x*μ y*C := by
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hK x y) (mul_nonneg (hμ x) (hμ y))
    _ = C := by
      simp only [mul_assoc,← mul_sum,← sum_mul,μ,fullPrimeMass_total,one_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothArithmeticTensor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite tensor expansion of the full smooth arithmetic weight -/

namespace JointDickman
open Finset

theorem geometricSmoothArithmeticSum_separated (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (r : ℤ → ℝ) (w₁ w₂ w₃ : ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S
      (fun k x y z => r k*w₁ x*w₂ y*w₃ z) g h =
      weightedGeometricArithmeticSum B j a b l u T t S r g h w₁ w₂ w₃ := by
  unfold geometricSmoothArithmeticSum weightedGeometricArithmeticSum
  simp only [mul_sum]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro n₂ _
  apply sum_congr rfl
  intro n₁ _
  split_ifs <;> ring

theorem geometricSmoothArithmeticSum_sum {ι : Type*} (I : Finset ι)
    (B j : ℕ) (a b l u T t : ℝ) (S : Finset ℤ)
    (W : ι → ℤ → ℝ → ℝ → ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S
      (fun k x y z => ∑ d ∈ I, W d k x y z) g h =
      ∑ d ∈ I, geometricSmoothArithmeticSum B j a b l u T t S (W d) g h := by
  classical
  unfold geometricSmoothArithmeticSum
  simp only [mul_sum]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro k _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro c _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro n₂ _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro n₁ _
  split_ifs <;> simp [mul_sum]

theorem geometricSmoothArithmeticSum_tensor (P : MvPolynomial (Fin 4) ℝ)
    (s : ℤ → ℝ) (B j : ℕ) (a b l u T t : ℝ) (S : Finset ℤ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S
      (fun k x y z => MvPolynomial.eval ![x,y,z,s k] P*
        tensorBoxBump x*tensorBoxBump y*tensorBoxBump z) g h =
      ∑ d ∈ P.support, weightedGeometricArithmeticSum B j a b l u T t S
        (fun k => P.coeff d*(s k)^(d 3)) g h
        (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2)) := by
  simp_rw [tensor_polynomial_expansion]
  rw [geometricSmoothArithmeticSum_sum]
  apply sum_congr rfl
  intro d _
  exact geometricSmoothArithmeticSum_separated _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothArithmeticError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive domination of smooth-weight approximation errors -/

namespace JointDickman
open Finset

theorem geometricSmoothArithmeticSum_sub (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (W V : ℤ → ℝ → ℝ → ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S (fun k x y z => W k x y z-V k x y z) g h =
      geometricSmoothArithmeticSum B j a b l u T t S W g h-
        geometricSmoothArithmeticSum B j a b l u T t S V g h := by
  unfold geometricSmoothArithmeticSum
  rw [← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro c _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n₂ _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n₁ _
  split_ifs <;> ring

theorem geometricSmoothArithmeticSum_smul (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (W : ℤ → ℝ → ℝ → ℝ → ℝ) (r : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    geometricSmoothArithmeticSum B j a b l u T t S (fun k x y z => r*W k x y z) g h =
      r*geometricSmoothArithmeticSum B j a b l u T t S W g h := by
  unfold geometricSmoothArithmeticSum
  simp only [mul_sum]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro n₂ _
  apply sum_congr rfl
  intro n₁ _
  split_ifs <;> ring

theorem geometricSmoothArithmeticSum_abs_le (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (W V : ℤ → ℝ → ℝ → ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (hWV : ∀ k ∈ S, ∀ x y z, |W k x y z| ≤ V k x y z) :
    |geometricSmoothArithmeticSum B j a b l u T t S W g h| ≤
      geometricSmoothArithmeticSum B j a b l u T t S V (fun _ => 1) (fun _ => 1) := by
  have hmass (f : (auxiliaryPrimes B → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) (n : ℕ) :
      |signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) f) n| ≤
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) (fun _ => 1)) n := by
    have hunit : subsetSiteTest (auxiliaryPrimes B) (fun _ => 1) = (fun _ => 1) := rfl
    rw [hunit,signedSplitProductMass_one]
    exact signedSplitProductMass_abs_le (auxiliaryPrimes_prime B) (fun _ _ => hf _) n
  have hmass0 (n : ℕ) :
      0 ≤ signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) (fun _ => 1)) n :=
    (abs_nonneg _).trans (hmass (fun _ => 1) (by simp) n)
  unfold geometricSmoothArithmeticSum
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro k hk
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro c _
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro n₂ _
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro n₁ _
  split_ifs
  · simp only [abs_mul,abs_of_nonneg (coefficientWeight_nonneg B c)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul (hmass g hg n₁) (hmass h hh n₂)
        (abs_nonneg _) (hmass0 _)) (coefficientWeight_nonneg B c))
      (hWV k hk _ _ _) (abs_nonneg _)
      (mul_nonneg (mul_nonneg (hmass0 n₁) (hmass0 n₂)) (coefficientWeight_nonneg B c))
  · simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UniformTensorApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform tensor approximation with its positive arithmetic error measure -/

namespace JointDickman
open Finset
open scoped Topology

theorem tensorCutoff_nonneg (x y z : ℝ) : 0 ≤ tensorCutoff x y z := by
  exact mul_nonneg (mul_nonneg tensorBoxBump.nonneg tensorBoxBump.nonneg)
    tensorBoxBump.nonneg

theorem tensorParameterBox_mem {x y z s : ℝ}
    (hx : x ∈ Set.Icc (1/4 : ℝ) (17/4)) (hy : y ∈ Set.Icc (1/4 : ℝ) (17/4))
    (hz : z ∈ Set.Icc (1/4 : ℝ) (17/4)) (hs : |s| ≤ 3) :
    ![x,y,z,s] ∈ tensorParameterBox := by
  constructor
  · intro i
    fin_cases i
    · exact hx.1
    · exact hy.1
    · exact hz.1
    · exact (abs_le.mp hs).1
  · intro i
    fin_cases i
    · exact hx.2
    · exact hy.2
    · exact hz.2
    · exact (abs_le.mp hs).2

theorem tensorBoxBump_zero_outside {x : ℝ} (hx : x ∉ Set.Icc (1/4 : ℝ) (17/4)) :
    tensorBoxBump x = 0 := by
  apply tensorBoxBump_zero
  by_cases h : x ≤ 1/4
  · exact Or.inl h
  · exact Or.inr (lt_of_not_ge (fun h' => hx ⟨by linarith,h'⟩))

theorem uniform_tensor_approximation (F : (Fin 4 → ℝ) → ℝ)
    (hF : ContinuousOn F tensorParameterBox) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 4) ℝ, ∀ s : ℝ, |s| ≤ 3 → ∀ x y z : ℝ,
      |F ![x,y,z,s]*tensorCutoff x y z-
        MvPolynomial.eval ![x,y,z,s] P*tensorCutoff x y z| ≤ ε*tensorCutoff x y z := by
  let f : C(tensorParameterBox,ℝ) :=
    ⟨fun p => F p,continuousOn_iff_continuous_domRestrict.mp hF⟩
  obtain ⟨P,hP⟩ := compact_support_polynomial_approximation tensorParameterBox isCompact_Icc f hε
  refine ⟨P,?_⟩
  intro s hs x y z
  by_cases hx : x ∈ Set.Icc (1/4 : ℝ) (17/4)
  · by_cases hy : y ∈ Set.Icc (1/4 : ℝ) (17/4)
    · by_cases hz : z ∈ Set.Icc (1/4 : ℝ) (17/4)
      · have hp := (hP ⟨![x,y,z,s],tensorParameterBox_mem hx hy hz hs⟩).le
        change |MvPolynomial.eval ![x,y,z,s] P-F ![x,y,z,s]| ≤ ε at hp
        rw [← sub_mul,abs_mul,abs_of_nonneg (tensorCutoff_nonneg _ _ _),abs_sub_comm]
        exact mul_le_mul_of_nonneg_right hp (tensorCutoff_nonneg _ _ _)
      · simp [tensorCutoff,tensorBoxBump_zero_outside hz]
    · simp [tensorCutoff,tensorBoxBump_zero_outside hy]
  · simp [tensorCutoff,tensorBoxBump_zero_outside hx]

theorem smooth_arithmetic_tensor_approximation (F : (Fin 4 → ℝ) → ℝ)
    (hF : ContinuousOn F tensorParameterBox) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 4) ℝ, ∀ (B j : ℕ) (a b l u T t : ℝ) (S : Finset ℤ)
      (s : ℤ → ℝ), (∀ k ∈ S, |s k| ≤ 3) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      |geometricSmoothArithmeticSum B j a b l u T t S
          (fun k x y z => F ![x,y,z,s k]*tensorCutoff x y z) g h-
        geometricSmoothArithmeticSum B j a b l u T t S
          (fun k x y z => MvPolynomial.eval ![x,y,z,s k] P*tensorCutoff x y z) g h| ≤
        ε*geometricSmoothArithmeticSum B j a b l u T t S
          (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1) := by
  obtain ⟨P,hP⟩ := uniform_tensor_approximation F hF hε
  refine ⟨P,?_⟩
  intro B j a b l u T t S s hs g h hg hh
  rw [← geometricSmoothArithmeticSum_sub,← geometricSmoothArithmeticSum_smul]
  exact geometricSmoothArithmeticSum_abs_le B j a b l u T t S _ _ g h hg hh
    (fun k hk x y z => hP (s k) (hs k hk) x y z)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothArithmeticMassBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive mass controlling smooth tensor-approximation errors -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem smooth_arithmetic_mass_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      T*geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1) ≤
        ε B+C*(T/j)*singularSeries j := by
  let w := tensorPowerFactor 0
  have hw (x : ℝ) : w x = tensorBoxBump x := by simp [w,tensorPowerFactor_apply]
  have hs : ∀ x, x ≤ 1/4 ∨ 17/4 < x → w x = 0 := tensorPowerFactor_support 0
  obtain ⟨c,hc,_,H,ε,hε,hbound⟩ := schwartz_arithmetic_feature_comparison hSD hSW hM hMP
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 17/4)
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 17/4)
    ht hη (by norm_num : (0 : ℝ) ≤ 1) w w w hs hs hs
  obtain ⟨m,hm,hcompare⟩ := hbound 1 (by norm_num)
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  let K₀ := (m : ℝ)^2*(2*((((1+Real.log (17/4)-Real.log (1/4))/t+1)*(D*1*1*1)))*
    (Real.log (17/4)-Real.log (1/4)+2))/channelMesh m
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hwidth : 0 ≤ 1+Real.log (17/4)-Real.log (1/4) := by linarith
  have hwidth' : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
  have hmesh := channelMesh_pos hm
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀] <;> positivity
  refine ⟨1+K₀,by positivity,ε,hε,?_⟩
  filter_upwards [hcompare,hden,eventually_ge_atTop 1] with B hb hd hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog
  let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
  let K := geometricWindowKernel m B t (Real.log (1/4)) (Real.log (17/4)) S
    (endpointSpatialWeight m B t (T/j) d w w w)
  let E := ∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
    primeCoarseKernel m B K x y
  let A := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1)
  have hdb : ∀ k ∈ S, |d k| ≤ D := by
    intro k hk
    apply hd.1
    apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
    nlinarith [(hlog k hk).1]
  have hwb (x : ℝ) : |w x| ≤ 1 := by
    rw [hw,abs_of_nonneg tensorBoxBump.nonneg]
    exact tensorBoxBump.le_one
  have hKb : ∀ x y, |primeCoarseKernel m B K x y| ≤ K₀ := by
    intro x y
    exact geometric_primeCoarseKernel_bound hm hB ht (by norm_num) (by norm_num)
      hD (by norm_num) (by norm_num) (by norm_num) S d w w w hdb hwb hwb hwb x y
  have hE : |E| ≤ K₀ := primeKernel_mean_abs_le B _ hKb
  have he := hb j Q hQ hscale hcut T hT hlag S hbox hlog
    (fun _ => 1) (by simp) (fun _ => 1) (fun _ => 1) (by simp) (by simp)
  have hA : A = weightedGeometricArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
      (fun _ => 1) (fun _ => 1) (fun _ => 1) w w w := by
    calc
      A = geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
          (fun _ x y z => 1*w x*w y*w z) (fun _ => 1) (fun _ => 1) := by
        dsimp only [A]
        congr 1
        funext k x y z
        simp [hw,tensorCutoff]
      _ = _ := geometricSmoothArithmeticSum_separated B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun _ => 1) w w w (fun _ => 1) (fun _ => 1)
  have he' : T*|A-(singularSeries j/(j : ℝ))*E| ≤ ε B+(T/j)*singularSeries j := by
    simpa only [hA,d,K,E,mul_one,one_mul] using he
  have hSp := (singularSeries_bounds hMP j).1
  have hscalar : 0 ≤ singularSeries j/(j : ℝ) := div_nonneg hSp (Nat.cast_nonneg j)
  have hE' : (singularSeries j/(j : ℝ))*E ≤ (singularSeries j/(j : ℝ))*K₀ :=
    mul_le_mul_of_nonneg_left ((le_abs_self E).trans hE) hscalar
  have hlinear := le_abs_self (A-(singularSeries j/(j : ℝ))*E)
  have hdiff := mul_le_mul_of_nonneg_left hlinear hT.le
  have hlast := mul_le_mul_of_nonneg_left hE' hT.le
  change T*A ≤ _
  have hid : T*((singularSeries j/(j : ℝ))*K₀) = K₀*(T/j)*singularSeries j := by ring
  rw [hid] at hlast
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PolynomialArithmeticFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite polynomial smooth weight has a finite prime-site kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem polynomialPrimeKernel_test (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T t : ℝ) (S : Finset ℤ) (s : ℤ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    (∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
      g x*h y*polynomialPrimeKernel P m B j c H T t S s x y) =
    ∑ d ∈ P.support, ∑ x, ∑ y,
      fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
        g x*h y*polynomialTermKernel P d (m d) B j (c d) (H d) T t S s x y := by
  classical
  simp only [polynomialPrimeKernel,mul_sum]
  conv_lhs => arg 2; ext x; rw [sum_comm]
  rw [sum_comm]

theorem polynomial_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H : (Fin 4 →₀ ℕ) → ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun k x y z => MvPolynomial.eval ![x,y,z,s k] P*
          tensorBoxBump x*tensorBoxBump y*tensorBoxBump z) g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*polynomialPrimeKernel P m B j c H T t S s x y)| ≤
        ε B+δ*(T/j)*singularSeries j := by
  classical
  let R := fun d : Fin 4 →₀ ℕ => |P.coeff d| *(3 : ℝ)^(d 3)
  have hex (d : Fin 4 →₀ ℕ) := schwartz_arithmetic_feature_comparison hSD hSW hM hMP
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 17/4)
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 17/4) ht hη
    (show 0 ≤ R d by positivity) (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1))
    (tensorPowerFactor (d 2)) (tensorPowerFactor_support _) (tensorPowerFactor_support _)
    (tensorPowerFactor_support _)
  choose c hc hcpos H e he hcompare using hex
  refine ⟨c,fun d => ⟨hc d,hcpos d⟩,H,fun B => ∑ d ∈ P.support, e d B,?_,?_⟩
  · simpa using tendsto_finsetSum P.support (fun d _ => he d)
  intro δ hδ
  let δ₀ := δ/((P.support.card : ℝ)+1)
  have hδ₀ : 0 < δ₀ := div_pos hδ (by positivity)
  choose m hm hB using fun d => hcompare d δ₀ hδ₀
  refine ⟨m,hm,?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun d _ => hB d)] with B hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  let A := fun d : Fin 4 →₀ ℕ => weightedGeometricArithmeticSum B j (1/4) (17/4) (1/4) (17/4)
    T t S (fun k => P.coeff d*(s k)^(d 3)) g h
    (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2))
  let K := fun d : Fin 4 →₀ ℕ => ∑ x, ∑ y,
    fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
      g x*h y*polynomialTermKernel P d (m d) B j (c d) (H d) T t S s x y
  have hlocal : ∀ d ∈ P.support,
      T*|A d-(singularSeries j/(j : ℝ))*K d| ≤ e d B+δ₀*(T/j)*singularSeries j := by
    intro d hd
    apply hB d hd j Q hQ hscale hcut T hT hlag S hbox hlog
      (fun k => P.coeff d*(s k)^(d 3)) _ g h hg hh
    intro k hk
    rw [abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hs k hk) _) (abs_nonneg _)
  rw [geometricSmoothArithmeticSum_tensor,polynomialPrimeKernel_test, mul_sum,← sum_sub_distrib]
  calc
    _ ≤ T*(∑ d ∈ P.support, |A d-(singularSeries j/(j : ℝ))*K d|) :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hT.le
    _ = ∑ d ∈ P.support, T*|A d-(singularSeries j/(j : ℝ))*K d| := mul_sum _ _ _
    _ ≤ ∑ d ∈ P.support, (e d B+δ₀*(T/j)*singularSeries j) := sum_le_sum hlocal
    _ = (∑ d ∈ P.support, e d B)+(P.support.card : ℝ)*δ₀*(T/j)*singularSeries j := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hcδ : (P.support.card : ℝ)*δ₀ ≤ δ := by
        change (P.support.card : ℝ)*(δ/((P.support.card : ℝ)+1)) ≤ δ
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (P.support.card : ℝ)+1)).mpr
        nlinarith
      have hSp := (singularSeries_bounds hMP j).1
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcδ (show 0 ≤ T/(j : ℝ) by positivity)) hSp
      linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_PolynomialKernelBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the compact smooth finite-feature kernels -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem polynomialTermKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) → ∀ x y,
        |polynomialTermKernel P d m B j c H T t S s x y| ≤ C := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,_,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,_,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,_,hM₂,_,hw₂,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let R := |P.coeff d| *(3 : ℝ)^(d 3)*D
  let C := (m : ℝ)^2*(2*((((1+Real.log (17/4)-Real.log (1/4))/t+1)*(R*M₀*M₁*M₂)))*
    (Real.log (17/4)-Real.log (1/4)+2))/channelMesh m
  have hR : 0 ≤ R := by positivity
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hw : 0 ≤ 1+Real.log (17/4)-Real.log (1/4) := by linarith
  have hw' : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
  have hmesh := channelMesh_pos hm
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j T S hlog s hs x y
  have hcoeff : ∀ k ∈ S, |(P.coeff d*(s k)^(d 3))*
      coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ R := by
    intro k hk
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog k hk]
    rw [abs_mul,abs_mul,abs_pow]
    apply mul_le_mul _ hden' (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hs k hk) _) (abs_nonneg _)
  exact geometric_primeCoarseKernel_bound hm hB ht (by norm_num) (by norm_num)
    hR hM₀ hM₁ hM₂ S _ _ _ _ hcoeff hw₀ hw₁ hw₂ x y

theorem polynomialPrimeKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (H : (Fin 4 →₀ ℕ) → ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) → ∀ x y,
        |polynomialPrimeKernel P m B j c H T t S s x y| ≤ C := by
  choose C hC hbound using fun d => polynomialTermKernel_bounded hM hMP P d (hm d) (c d) (hc d) (H d) ht
  refine ⟨∑ d ∈ P.support, C d,sum_nonneg (fun d _ => hC d),?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun d _ => hbound d)] with B hb
  intro j T S hlog s hs x y
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun d hd => hb d hd j T S hlog s hs x y))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothArithmeticFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact smooth arithmetic weights have finite prime-site approximations -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem smooth_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (F : (Fin 4 → ℝ) → ℝ) (hF : ContinuousOn F tensorParameterBox)
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun k x y z => F ![x,y,z,s k]*tensorCutoff x y z) g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*polynomialPrimeKernel P m B j c H T t S s x y)| ≤
        ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |polynomialPrimeKernel P m B j c H T t S s x y| ≤ C₀ := by
  obtain ⟨C,hC,ε₀,hε₀,hmass⟩ := smooth_arithmetic_mass_bound hSD hSW hM hMP ht hη
  intro δ hδ
  let α := δ/(2*(C+1))
  have hα : 0 < α := div_pos hδ (by positivity)
  obtain ⟨P,hP⟩ := smooth_arithmetic_tensor_approximation F hF hα
  obtain ⟨c,hc,H,ε₁,hε₁,hpoly⟩ := polynomial_arithmetic_feature_comparison
    hSD hSW hM hMP P ht hη
  obtain ⟨m,hm,hpolyB⟩ := hpoly (δ/2) (by positivity)
  obtain ⟨C₀,hC₀,hbounded⟩ := polynomialPrimeKernel_bounded hM hMP P m hm c
    (fun d => (hc d).1) H ht
  refine ⟨P,c,hc,H,m,hm,C₀,hC₀,fun B => α*ε₀ B+ε₁ B,?_,?_⟩
  · simpa using (hε₀.const_mul α).add hε₁
  filter_upwards [hmass,hpolyB,hbounded] with B hmassB hpolyB hkb
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  let A := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun k x y z => F ![x,y,z,s k]*tensorCutoff x y z) g h
  let Aₚ := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun k x y z => MvPolynomial.eval ![x,y,z,s k] P*tensorCutoff x y z) g h
  let V := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1)
  let K := (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
    fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
      g x*h y*polynomialPrimeKernel P m B j c H T t S s x y)
  have hap : |A-Aₚ| ≤ α*V := hP B j _ _ _ _ T t S s hs g h hg hh
  have hvol : T*V ≤ ε₀ B+C*(T/j)*singularSeries j :=
    hmassB j Q hQ hscale hcut T hT hlag S hbox hlog
  have hp : T*|Aₚ-K| ≤ ε₁ B+(δ/2)*(T/j)*singularSeries j := by
    simpa only [Aₚ,K,tensorCutoff,mul_assoc] using
      hpolyB j Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  have happrox : T*|A-Aₚ| ≤ α*(ε₀ B+C*(T/j)*singularSeries j) := by
    calc
      _ ≤ T*(α*V) := mul_le_mul_of_nonneg_left hap hT.le
      _ = α*(T*V) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvol hα.le
  have hbudget : α*C+δ/2 ≤ δ := by
    have haC : α*C ≤ δ/2 := calc
      α*C ≤ α*(C+1) := mul_le_mul_of_nonneg_left (by linarith) hα.le
      _ = δ/2 := by dsimp [α]; field_simp
    linarith
  have hSp := (singularSeries_bounds hMP j).1
  have hbudget' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbudget (show 0 ≤ T/(j : ℝ) by positivity)) hSp
  constructor
  · change T*|A-K| ≤ _
    have htri := mul_le_mul_of_nonneg_left (abs_sub_le A Aₚ K) hT.le
    nlinarith
  · exact hkb j T S (fun k hk => (hlog k hk).1) s hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothDyadicPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete smooth geometric partition of unity -/

namespace JointDickman
open Finset
open scoped SchwartzMap

theorem dyadicPartitionWeight_zero {x : ℝ} (hx : x ≤ 1/2 ∨ 2 < x) :
    dyadicPartitionWeight x = 0 := by
  unfold dyadicPartitionWeight
  rcases hx with h | h
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith),sub_self]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith),sub_self]

theorem dyadicPartitionWeight_bounds (x : ℝ) :
    0 ≤ dyadicPartitionWeight x ∧ dyadicPartitionWeight x ≤ 1 := by
  by_cases hx : x ≤ 1/2
  · rw [dyadicPartitionWeight_zero (Or.inl hx)]
    norm_num
  · have hx0 : 0 ≤ x := by linarith
    unfold dyadicPartitionWeight
    have hm := Real.smoothTransition.monotone (show 2-2*x ≤ 2-x by linarith)
    have h0 := Real.smoothTransition.nonneg (2-2*x)
    have h1 := Real.smoothTransition.le_one (2-x)
    constructor <;> linarith

theorem dyadicPartitionWeight_smooth : ContDiff ℝ (⊤ : ℕ∞) dyadicPartitionWeight := by
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).sub
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem dyadicPartition_step (z : ℝ) (k : ℕ) :
    dyadicPartitionWeight (z/(2 : ℝ)^(k+1)) =
      Real.smoothTransition (2-z/(2 : ℝ)^(k+1))-
        Real.smoothTransition (2-z/(2 : ℝ)^k) := by
  unfold dyadicPartitionWeight
  have he : 2*(z/(2 : ℝ)^(k+1)) = z/(2 : ℝ)^k := by rw [pow_succ]; field_simp
  rw [he]

theorem dyadicPartition_sum {L U : ℕ} (hLU : L ≤ U) (z : ℝ)
    (hlo : 2 ≤ z/(2 : ℝ)^L) (hhi : z/(2 : ℝ)^U ≤ 1) :
    (∑ k ∈ Ico L U, dyadicPartitionWeight (z/(2 : ℝ)^(k+1))) = 1 := by
  simp_rw [dyadicPartition_step]
  rw [sum_Ico_sub (fun k => Real.smoothTransition (2-z/(2 : ℝ)^k)) hLU]
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_AmplificationTensorProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual amplification weight in normalized geometric-box coordinates -/

namespace JointDickman
open scoped Topology

theorem amplificationTensorProfile_continuous :
    ContinuousOn amplificationTensorProfile tensorParameterBox := by
  have hv (i : Fin 4) : ContinuousOn (fun v : Fin 4 → ℝ => v i) tensorParameterBox :=
    (continuous_apply i).continuousOn
  have hz : ∀ v ∈ tensorParameterBox, v 2 ≠ 0 := by
    intro v hv
    have hh : (1/4 : ℝ) ≤ v 2 := hv.1 2
    linarith
  exact (amplificationBump.continuous.comp_continuousOn (hv 3)).mul
    (((amplificationBump.continuous.comp_continuousOn ((hv 0).div (hv 2) hz)).mul
      (amplificationBump.continuous.comp_continuousOn ((hv 1).div (hv 2) hz))).mul
      (dyadicPartitionWeight_smooth.continuous.comp_continuousOn (hv 2)))

theorem amplificationSpatialProfile_bounds (x y z : ℝ) :
    0 ≤ amplificationSpatialProfile x y z ∧ amplificationSpatialProfile x y z ≤ 1 := by
  obtain ⟨ha,ha'⟩ := amplificationBump_bounds (x/z)
  obtain ⟨hb,hb'⟩ := amplificationBump_bounds (y/z)
  obtain ⟨hc,hc'⟩ := dyadicPartitionWeight_bounds z
  exact ⟨mul_nonneg (mul_nonneg ha hb) hc,
    (mul_le_mul (mul_le_mul ha' hb' hb zero_le_one) hc' hc (by norm_num)).trans_eq (by ring)⟩

theorem amplificationSpatialProfile_support {x y z : ℝ}
    (h : amplificationSpatialProfile x y z ≠ 0) : x ∈ Set.Icc (1/2 : ℝ) 4 ∧ y ∈ Set.Icc (1/2 : ℝ) 4 ∧
      z ∈ Set.Icc (1/2 : ℝ) 2 := by
  have hprod : amplificationBump (x/z)*amplificationBump (y/z) ≠ 0 :=
    left_ne_zero_of_mul h
  have hx := amplificationBump_support (left_ne_zero_of_mul hprod)
  have hy := amplificationBump_support (right_ne_zero_of_mul hprod)
  have hz : dyadicPartitionWeight z ≠ 0 := right_ne_zero_of_mul h
  have hzlo : (1/2 : ℝ) < z := by
    by_contra hn
    exact hz (dyadicPartitionWeight_zero (Or.inl (le_of_not_gt hn)))
  have hzhi : z ≤ 2 := by
    by_contra hn
    exact hz (dyadicPartitionWeight_zero (Or.inr (lt_of_not_ge hn)))
  have hzpos : 0 < z := by linarith
  have hxb : x ∈ Set.Icc (1/2 : ℝ) 4 := by
    constructor
    · have he := (lt_div_iff₀ hzpos).mp hx.1
      nlinarith
    · have he := (div_lt_iff₀ hzpos).mp hx.2
      nlinarith
  have hyb : y ∈ Set.Icc (1/2 : ℝ) 4 := by
    constructor
    · have he := (lt_div_iff₀ hzpos).mp hy.1
      nlinarith
    · have he := (div_lt_iff₀ hzpos).mp hy.2
      nlinarith
  exact ⟨hxb,hyb,⟨hzlo.le,hzhi⟩⟩

theorem amplificationSpatialProfile_cutoff {x y z : ℝ}
    (h : amplificationSpatialProfile x y z ≠ 0) : tensorCutoff x y z = 1 := by
  obtain ⟨hx,hy,hz⟩ := amplificationSpatialProfile_support h
  rw [tensorCutoff,tensorBoxBump_one hx,tensorBoxBump_one hy,
    tensorBoxBump_one ⟨hz.1,hz.2.trans (by norm_num)⟩]
  norm_num

theorem amplificationTensorProfile_cutoff (s x y z : ℝ) :
    amplificationTensorProfile ![x,y,z,s]*tensorCutoff x y z =
      amplificationTensorProfile ![x,y,z,s] := by
  by_cases h : amplificationSpatialProfile x y z = 0
  · simp [amplificationTensorProfile,h]
  · rw [amplificationSpatialProfile_cutoff h,mul_one]

theorem amplificationBump_lipschitz :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : ℝ, |amplificationBump y-amplificationBump x| ≤ D*|y-x| := by
  let w := amplificationBump_compactSupport.toSchwartzMap amplificationBump_contDiff
  obtain ⟨_,D,_,hD,_,hd,_⟩ := schwartz_value_derivative_bounds w
  refine ⟨D,hD,?_⟩
  intro x y
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := (w : ℝ → ℝ)) (f' := deriv w) (s := Set.univ)
    (fun x _ => (w.hasDerivAt x).hasDerivWithinAt)
    (fun x _ => by simpa only [Real.norm_eq_abs] using hd x)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  have heq (z : ℝ) : w z = amplificationBump z := rfl
  rw [heq,heq] at he
  simpa only [Real.norm_eq_abs] using he

theorem amplificationBoxWeight_freezing :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 0 < B → ∀ s x y z : ℝ,
      |amplificationBoxWeight B s x y z-amplificationTensorProfile ![x,y,z,s]| ≤
        (C/B)*tensorCutoff x y z := by
  obtain ⟨D,hD,hlip⟩ := amplificationBump_lipschitz
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨D*Real.log 2,mul_nonneg hD hlog2,?_⟩
  intro B hB s x y z
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  change |amplificationBump (s+Real.log z/B)*amplificationSpatialProfile x y z-
    amplificationBump s*amplificationSpatialProfile x y z| ≤ _
  by_cases h : amplificationSpatialProfile x y z = 0
  · simp only [h,mul_zero,sub_self,abs_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg hD hlog2) hBr.le) (tensorCutoff_nonneg _ _ _)
  · have hcut := amplificationSpatialProfile_cutoff h
    have hz : dyadicPartitionWeight z ≠ 0 := right_ne_zero_of_mul h
    have hzlo : (1/2 : ℝ) < z := by
      by_contra hn
      exact hz (dyadicPartitionWeight_zero (Or.inl (le_of_not_gt hn)))
    have hzhi : z ≤ 2 := by
      by_contra hn
      exact hz (dyadicPartitionWeight_zero (Or.inr (lt_of_not_ge hn)))
    have hzpos : 0 < z := by linarith
    have hlog : |Real.log z| ≤ Real.log 2 := by
      rw [abs_le]
      constructor
      · have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hzlo.le
        rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
        exact hh
      · exact Real.log_le_log hzpos hzhi
    have hdiff := hlip s (s+Real.log z/B)
    rw [add_sub_cancel_left,abs_div,abs_of_pos hBr] at hdiff
    have hmain : |amplificationBump (s+Real.log z/B)-amplificationBump s| ≤ D*Real.log 2/B := by
      exact hdiff.trans (by apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hBr.le) hD).trans_eq; ring)
    have hp := amplificationSpatialProfile_bounds x y z
    rw [← sub_mul,abs_mul,abs_of_nonneg hp.1,hcut,mul_one]
    exact (mul_le_mul hmain hp.2 hp.1 (by positivity)).trans_eq (mul_one _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationBoxFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite prime-site approximation for the actual smooth amplification box weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_box_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun k x y z => amplificationBoxWeight B (s k) x y z) g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*polynomialPrimeKernel P m B j c H T t S s x y)| ≤
        ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |polynomialPrimeKernel P m B j c H T t S s x y| ≤ C₀ := by
  obtain ⟨C,hC,hfreeze⟩ := amplificationBoxWeight_freezing
  obtain ⟨D,hD,ε₀,hε₀,hmass⟩ := smooth_arithmetic_mass_bound hSD hSW hM hMP ht hη
  have hrate : Tendsto (fun B : ℕ => C/(B : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  intro δ hδ
  obtain ⟨P,c,hc,H,m,hm,C₀,hC₀,ε₁,hε₁,hcompare⟩ := smooth_arithmetic_feature_comparison
    hSD hSW hM hMP amplificationTensorProfile amplificationTensorProfile_continuous ht hη
    (δ/2) (by positivity)
  have hbudget : ∀ᶠ B : ℕ in atTop, (C/(B : ℝ))*D ≤ δ/2 :=
    (hrate.mul_const D).eventually_le_const (by simpa using half_pos hδ)
  refine ⟨P,c,hc,H,m,hm,C₀,hC₀,fun B => ε₁ B+(C/(B : ℝ))*ε₀ B,?_,?_⟩
  · simpa using hε₁.add (hrate.mul hε₀)
  filter_upwards [hcompare,hmass,hbudget,eventually_gt_atTop 0] with B hb hmassB hbud hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  obtain ⟨hcomp,hbound⟩ := hb j Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  refine ⟨?_,hbound⟩
  let A := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun k x y z => amplificationBoxWeight B (s k) x y z) g h
  let A₀ := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun k x y z => amplificationTensorProfile ![x,y,z,s k]*tensorCutoff x y z) g h
  let V := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1)
  let K := (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
    fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
      polynomialPrimeKernel P m B j c H T t S s x y)
  have hdiff : |A-A₀| ≤ (C/(B : ℝ))*V := by
    change |geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S _ g h-
      geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S _ g h| ≤ _
    rw [← geometricSmoothArithmeticSum_sub,← geometricSmoothArithmeticSum_smul]
    apply geometricSmoothArithmeticSum_abs_le _ _ _ _ _ _ _ _ _ _ _ g h hg hh
    intro k _ x y z
    rw [amplificationTensorProfile_cutoff]
    exact hfreeze B hB (s k) x y z
  have hV : T*V ≤ ε₀ B+D*(T/j)*singularSeries j :=
    hmassB j Q hQ hscale hcut T hT hlag S hbox hlog
  have hdiff' : T*|A-A₀| ≤ (C/(B : ℝ))*(ε₀ B+D*(T/j)*singularSeries j) := by
    calc
      _ ≤ T*((C/(B : ℝ))*V) := mul_le_mul_of_nonneg_left hdiff hT.le
      _ = (C/(B : ℝ))*(T*V) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hV (div_nonneg hC (Nat.cast_nonneg B))
  have hSp := (singularSeries_bounds hMP j).1
  have hbud' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbud (show 0 ≤ T/(j : ℝ) by positivity)) hSp
  have hcomp' : T*|A₀-K| ≤ ε₁ B+(δ/2)*(T/j)*singularSeries j := hcomp
  change T*|A-K| ≤ _
  have htri := mul_le_mul_of_nonneg_left (abs_sub_le A A₀ K) hT.le
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteTripleExtension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite extension of an arithmetic triple sum by zero -/

namespace JointDickman
open Finset

theorem finite_triple_sum_extend {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A A' : Finset α} {C C' : Finset β} (hA : A ⊆ A') (hC : C ⊆ C')
    (f : β → α → α → ℝ)
    (hsupp : ∀ c b a, f c b a ≠ 0 → c ∈ C ∧ b ∈ A ∧ a ∈ A) :
    (∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, f c b a) =
      ∑ c ∈ C', ∑ b ∈ A', ∑ a ∈ A', f c b a := by
  calc
    _ = ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A', f c b a := by
      apply sum_congr rfl
      intro c _
      apply sum_congr rfl
      intro b _
      apply sum_subset hA
      intro a _ ha
      by_contra h
      exact ha (hsupp c b a h).2.2
    _ = ∑ c ∈ C, ∑ b ∈ A', ∑ a ∈ A', f c b a := by
      apply sum_congr rfl
      intro c _
      apply sum_subset hA
      intro b _ hb
      apply sum_eq_zero
      intro a _
      by_contra h
      exact hb (hsupp c b a h).2.1
    _ = _ := by
      apply sum_subset hC
      intro c _ hc
      apply sum_eq_zero
      intro b _
      apply sum_eq_zero
      intro a _
      by_contra h
      exact hc (hsupp c b a h).1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricDyadicPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic recombination of the original amplification weight -/

namespace JointDickman
open Finset

theorem exp_nat_log_two (k : ℕ) : Real.exp ((k : ℝ)*Real.log 2) = (2 : ℝ)^k := by
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem geometric_dyadic_partition {L U : ℕ} (hLU : L ≤ U) (z : ℝ)
    (hlo : 2 ≤ z/(2 : ℝ)^L) (hhi : z/(2 : ℝ)^U ≤ 1) :
    (∑ k ∈ dyadicBoxIndices L U, dyadicPartitionWeight (z/Real.exp ((k : ℝ)*Real.log 2))) = 1 := by
  classical
  rw [dyadicBoxIndices,sum_image]
  · simpa only [Int.cast_natCast,exp_nat_log_two] using dyadicPartition_sum hLU z hlo hhi
  · intro a _ b _ h
    exact Nat.add_right_cancel (Int.ofNat_inj.mp h)

theorem amplificationBoxWeight_normalized (B : ℕ) {T N c : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hc : 0 < c) (a b : ℝ) :
    amplificationBoxWeight B (Real.log (N/T)/B) (a/N) (b/N) (c/(N/T)) =
      amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c))*dyadicPartitionWeight (c/(N/T)) := by
  have hX := div_pos hN hT
  have hlog : Real.log (N/T)/B+Real.log (c/(N/T))/B = Real.log c/B := by
    rw [Real.log_div hc.ne' hX.ne']
    ring
  have ha : (a/N)/(c/(N/T)) = a/(T*c) := by field_simp
  have hb : (b/N)/(c/(N/T)) = b/(T*c) := by field_simp
  simp only [amplificationBoxWeight,amplificationSpatialProfile,hlog,ha,hb]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationBoxSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact support of the amplification integrand in each geometric box -/

namespace JointDickman
open Finset

theorem mem_tensor_interval_of_ratio {n : ℕ} {N : ℝ} (hN : 0 < N)
    (hn : (n : ℝ)/N ∈ Set.Icc (1/2 : ℝ) 4) :
    n ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  have hlo := (le_div_iff₀ hN).mp hn.1
  have hhi := (div_le_iff₀ hN).mp hn.2
  apply mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (show 0 ≤ (1/4 : ℝ)*N by positivity)).mpr
    nlinarith
  · apply (Nat.le_floor_iff (show 0 ≤ (17/4 : ℝ)*N by positivity)).mpr
    nlinarith

theorem amplificationBoxWeight_integer_support (B : ℕ) {T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) (s : ℝ) (a b c : ℕ)
    (hw : amplificationBoxWeight B s (a/N) (b/N) (c/(N/T)) ≠ 0) :
    c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊ ∧
    a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ ∧
    b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  obtain ⟨ha,hb,hc⟩ := amplificationSpatialProfile_support (right_ne_zero_of_mul hw)
  exact ⟨mem_tensor_interval_of_ratio (div_pos hN hT) ⟨hc.1,hc.2.trans (by norm_num)⟩,
    mem_tensor_interval_of_ratio hN ha,mem_tensor_interval_of_ratio hN hb⟩

theorem amplificationBoxTerm_support (B j : ℕ) {T N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ)
    (hf : amplificationBoxTerm B j T N g h c b a ≠ 0) :
    c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊ ∧
    b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ ∧
    a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  have hw : amplificationBoxWeight B (Real.log (N/T)/B) (a/N) (b/N) (c/(N/T)) ≠ 0 := by
    intro hz
    apply hf
    simp only [amplificationBoxTerm,hz,mul_zero,ite_self]
  obtain ⟨hc,ha,hb⟩ := amplificationBoxWeight_integer_support B hT hN _ a b c hw
  exact ⟨hc,hb,ha⟩

theorem amplificationBoxTerm_eq (B j : ℕ) {T N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) :
    amplificationBoxTerm B j T N g h c b a =
      amplificationArithmeticTerm B j T g h c b a*dyadicPartitionWeight (c/(N/T)) := by
  by_cases hc : c = 0
  · simp [amplificationBoxTerm,amplificationArithmeticTerm,hc,coefficientWeight]
  · have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
    unfold amplificationBoxTerm amplificationArithmeticTerm
    rw [amplificationBoxWeight_normalized B hT hN hcpos]
    split_ifs <;> ring


theorem amplificationArithmeticTerm_log_support {B : ℕ} (hB : 0 < B) (j : ℕ) (T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ)
    (hf : amplificationArithmeticTerm B j T g h c b a ≠ 0) :
    (B : ℝ) ≤ Real.log c ∧ Real.log c ≤ 2*B := by
  have hne : amplificationBump (Real.log c/B) ≠ 0 := by
    intro hz
    apply hf
    simp [amplificationArithmeticTerm,hz]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := amplificationBump_support hne
  have hlo := (lt_div_iff₀ hBr).mp hh.1
  have hhi := (div_lt_iff₀ hBr).mp hh.2
  constructor <;> nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_DyadicScaleWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete dyadic indices in the manuscript's scale window -/

namespace JointDickman
open Finset

theorem dyadic_scale_window {B : ℕ} (hB : 30 ≤ B) {T : ℝ} (hT : 1 ≤ T)
    (hlogT : Real.log T ≤ (B : ℝ)/10) :
    dyadicBoxLower B T ≤ dyadicBoxUpper B T ∧
    (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      (k : ℝ)*Real.log 2 ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) ∧
      Real.log (Real.exp ((k : ℝ)*Real.log 2)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) ∧
    (∀ c : ℝ, 0 < c → (B : ℝ) ≤ Real.log c → Real.log c ≤ 2*B →
      2 ≤ (c*T)/(2 : ℝ)^(dyadicBoxLower B T) ∧
      (c*T)/(2 : ℝ)^(dyadicBoxUpper B T) ≤ 1) := by
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    simpa only [show (2 : ℝ)-1 = 1 by norm_num] using Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  let v := ((B : ℝ)+Real.log T)/Real.log 2
  let w := (2*(B : ℝ)+Real.log T)/Real.log 2
  have hv : (1 : ℝ) ≤ v := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  have hw : 0 ≤ w := by dsimp [w] <;> positivity
  have hvw : v ≤ w := by dsimp [v,w]; gcongr; linarith
  have hf1 : 1 ≤ ⌊v⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ v)).mpr (by simpa only [Nat.cast_one] using hv)
  have hL : dyadicBoxLower B T+1 = ⌊v⌋₊ := Nat.sub_add_cancel hf1
  have hU : dyadicBoxUpper B T = ⌈w⌉₊+1 := rfl
  have hfloor := Nat.floor_le (show 0 ≤ v by linarith)
  have hfloor' := Nat.lt_floor_add_one v
  have hceil := Nat.le_ceil w
  have hceil' := Nat.ceil_lt_add_one hw
  have hfv : (⌊v⌋₊ : ℝ)*Real.log 2 ≤ (B : ℝ)+Real.log T := by
    have hm := mul_le_mul_of_nonneg_right hfloor hl2.le
    simpa only [v,div_mul_cancel₀ _ hl2.ne'] using hm
  have hfv' : (B : ℝ)+Real.log T-Real.log 2 < (⌊v⌋₊ : ℝ)*Real.log 2 := by
    have hm := mul_lt_mul_of_pos_right hfloor' hl2
    dsimp only [v] at hm
    rw [div_mul_cancel₀ _ hl2.ne'] at hm
    nlinarith
  have hcw : 2*(B : ℝ)+Real.log T ≤ (dyadicBoxUpper B T : ℝ)*Real.log 2 := by
    have hm := mul_le_mul_of_nonneg_right hceil hl2.le
    dsimp only [w] at hm
    rw [div_mul_cancel₀ _ hl2.ne'] at hm
    rw [hU,Nat.cast_add,Nat.cast_one]
    nlinarith
  have hcw' : (dyadicBoxUpper B T : ℝ)*Real.log 2 < 2*(B : ℝ)+Real.log T+2*Real.log 2 := by
    have hm := mul_lt_mul_of_pos_right hceil' hl2
    dsimp only [w] at hm
    rw [add_mul,div_mul_cancel₀ _ hl2.ne',one_mul] at hm
    rw [hU,Nat.cast_add,Nat.cast_one]
    nlinarith
  have hLU : dyadicBoxLower B T ≤ dyadicBoxUpper B T := by
    have hh := (Nat.floor_mono hvw).trans (Nat.floor_le_ceil w)
    dsimp only [dyadicBoxLower,dyadicBoxUpper]
    exact (Nat.sub_le _ _).trans (hh.trans (Nat.le_succ _))
  refine ⟨hLU,?_,?_⟩
  · intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    obtain ⟨hnL,hnU⟩ := mem_Ico.mp hn
    have hlo : ⌊v⌋₊ ≤ n+1 := by rw [← hL]; omega
    have hhi : n+1 ≤ dyadicBoxUpper B T := by omega
    have hlo' : (⌊v⌋₊ : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast hlo
    have hhi' : ((n+1 : ℕ) : ℝ) ≤ dyadicBoxUpper B T := by exact_mod_cast hhi
    have hlo'' := mul_le_mul_of_nonneg_right hlo' hl2.le
    have hhi'' := mul_le_mul_of_nonneg_right hhi' hl2.le
    have hlog : Real.log (Real.exp (((n+1 : ℕ) : ℝ)*Real.log 2)/T) =
        ((n+1 : ℕ) : ℝ)*Real.log 2-Real.log T := by
      rw [Real.log_div (Real.exp_pos _).ne' hTpos.ne',Real.log_exp]
    simp only [Int.cast_natCast]
    rw [hlog]
    constructor <;> constructor <;> nlinarith
  · intro c hc hclo hchi
    have hct := mul_pos hc hTpos
    have hlogct : Real.log (c*T) = Real.log c+Real.log T := Real.log_mul hc.ne' hTpos.ne'
    constructor
    · apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
      have hh : (2 : ℝ)^(dyadicBoxLower B T+1) ≤ c*T := by
        rw [← exp_nat_log_two,← Real.exp_log hct]
        apply Real.exp_le_exp.mpr
        rw [hlogct,hL]
        exact hfv.trans (by linarith)
      simpa only [pow_succ,mul_comm] using hh
    · apply (div_le_one (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
      rw [← exp_nat_log_two,← Real.exp_log hct]
      apply Real.exp_le_exp.mpr
      rw [hlogct]
      exact (show Real.log c+Real.log T ≤ 2*(B : ℝ)+Real.log T by linarith).trans hcw

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationDyadicIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact reconstruction of the unpartitioned amplification triple sum -/

namespace JointDickman
open Finset

theorem sum_triple_interchange {ι α β : Type*} (S : Finset ι) (A : Finset α) (C : Finset β)
    (f : ι → β → α → α → ℝ) :
    (∑ k ∈ S, ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, f k c b a) =
      ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, ∑ k ∈ S, f k c b a := by
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  exact sum_comm

theorem amplification_dyadic_identity {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlogT : Real.log T ≤ (B : ℝ)/10) (j U V : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hU : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U)
    (hV : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) :
    geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T (Real.log 2)
      (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
      (fun k x y z => amplificationBoxWeight B (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B) x y z)
      g h = amplificationArithmeticSum B j T U V g h := by
  have hTpos := lt_of_lt_of_le zero_lt_one hT
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  obtain ⟨hLU,_,hbracket⟩ := dyadic_scale_window hB hT hlogT
  unfold geometricSmoothArithmeticSum amplificationArithmeticSum
  congr 1
  change (∑ k ∈ S,
      ∑ c ∈ Ioc ⌊(1/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊
        ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊,
      ∑ b ∈ Ioc ⌊(1/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊,
      ∑ a ∈ Ioc ⌊(1/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊,
        amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a) = _
  calc
    _ = ∑ k ∈ S, ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a := by
      apply sum_congr rfl
      intro k hk
      apply finite_triple_sum_extend
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hU k hk)⟩
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hV k hk)⟩
      · exact amplificationBoxTerm_support B j hTpos (Real.exp_pos _) g h
    _ = ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        ∑ k ∈ S, amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a :=
      sum_triple_interchange S (Ioc 0 U) (Ioc 0 V) _
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      simp_rw [amplificationBoxTerm_eq B j hTpos (Real.exp_pos _) g h c b a,div_div_eq_mul_div]
      rw [← mul_sum]
      by_cases he : amplificationArithmeticTerm B j T g h c b a = 0
      · simp [he]
      · have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
        obtain ⟨hlo,hhi⟩ := amplificationArithmeticTerm_log_support hBp j T g h c b a he
        have hcp : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
        obtain ⟨hcl,hcu⟩ := hbracket c hcp hlo hhi
        rw [geometric_dyadic_partition hLU (c*T) hcl hcu,mul_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationArithmeticFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original amplification arithmetic sum has a bounded finite-feature kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {η : ℝ} (hη : 0 < η) :
    ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
      ∀ U V : ℕ,
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|amplificationArithmeticSum B j T U V g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
            amplificationPrimeKernel P m B j c H T x y)| ≤ ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |amplificationPrimeKernel P m B j c H T x y| ≤ C₀ := by
  intro δ hδ
  obtain ⟨P,c,hc,H,m,hm,C₀,hC₀,ε,hε,hcompare⟩ := amplification_box_feature_comparison
    hSD hSW hM hMP (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hη δ hδ
  refine ⟨P,c,hc,H,m,hm,C₀,hC₀,ε,hε,?_⟩
  filter_upwards [hcompare,eventually_ge_atTop 30] with B hb hB
  intro j _ Q hQ hscale hcut T hT hlogT hlag U V hU hV g h hg hh
  obtain ⟨_,hwindow,_⟩ := dyadic_scale_window hB hT hlogT
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  let s := fun k : ℤ => Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 30) hB)
  have hs : ∀ k ∈ S, |s k| ≤ 3 := by
    intro k hk
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ hBpos).mpr
      nlinarith [(hwindow k hk).2.1]
    · apply (div_le_iff₀ hBpos).mpr
      nlinarith [(hwindow k hk).2.2]
  have he := hb j Q hQ hscale hcut T (lt_of_lt_of_le zero_lt_one hT) hlag S
    (fun k hk => (hwindow k hk).1) (fun k hk => (hwindow k hk).2) s hs g h hg hh
  rw [amplification_dyadic_identity hB hT hlogT j U V g h hU hV] at he
  exact he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationPositiveMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Total positive arithmetic mass for removing remainder restrictions -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_positive_mass_bound_jd_oai
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ j : ℕ, [NeZero j] →
        ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
        ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
        ∀ U V : ℕ,
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          T*amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) ≤
            ε B+K*(T/j)*singularSeries j := by
  obtain ⟨P,c,hc,H,m,hm,K,hK,ε,hε,hcomp⟩ :=
    amplification_arithmetic_feature_comparison hSD hSW hM hMP hη 1 (by norm_num)
  refine ⟨K+1,by linarith,ε,hε,?_⟩
  filter_upwards [hcomp] with B hb
  intro j _ Q hQ hscale hcut T hT hlog hlag U V hU hV
  obtain ⟨he,hkernel⟩ := hb j Q hQ hscale hcut T hT hlog hlag U V hU hV
    (fun _ => 1) (fun _ => 1) (by simp) (by simp)
  let E := ∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*
    fullPrimeMass (auxiliaryPrimes B) y*amplificationPrimeKernel P m B j c H T x y
  have hE : |E| ≤ K := primeKernel_mean_abs_le B _ hkernel
  have hSp := (singularSeries_bounds hMP j).1
  have hscalar : 0 ≤ singularSeries j/(j : ℝ) := div_nonneg hSp (Nat.cast_nonneg _)
  have hmodel : T*((singularSeries j/(j : ℝ))*E) ≤ T*((singularSeries j/(j : ℝ))*K) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ((le_abs_self E).trans hE) hscalar)
      (lt_of_lt_of_le zero_lt_one hT).le
  have herr : T*(amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1)-
      (singularSeries j/(j : ℝ))*E) ≤ ε B+(T/j)*singularSeries j := by
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) (lt_of_lt_of_le zero_lt_one hT).le).trans
      (by simpa only [mul_one,one_mul] using he)
  have hid : T*((singularSeries j/(j : ℝ))*K) = K*(T/j)*singularSeries j := by ring
  rw [hid] at hmodel
  nlinarith

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.amplification_positive_mass_bound_jd_oai := @OAI.JointDickman.amplification_positive_mass_bound_jd_oai
