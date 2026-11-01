-- Prove2me | solution 1 for OAI.JointDickman.counting_model_energy_mean_proved_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:33:43.045197+00:00
-- url     : https://prove2.me/submissions/53073b37-6e5a-479b-9004-6c739ea8b62b

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_coarse_residue_smoothing_energy_proved_jd

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

theorem fairRetentionMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) : 0 ≤ fairRetentionMass x y :=
  finiteProductMass_nonneg _ (fun i => fairRetentionBitMass_nonneg (x i)) y

theorem fairRetentionMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) : ∑ y, fairRetentionMass x y = 1 :=
  finiteProductMass_sum _ (fun i => fairRetentionBitMass_sum (x i))

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The singular series produced by the Ramanujan residue factor -/

namespace JointDickman
open Finset Filter
open scoped Topology ArithmeticFunction.Moebius

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

theorem singularSeriesTail_tendsto_zero :
    Tendsto singularSeriesTail atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun q : ℕ => 1/(q.totient : ℝ)^2)

theorem singularSeries_tail_bound (hMP : PublishedInputs.PrimeProductMertensInput)
    (j Q : ℕ) :
    ‖(∑' q, singularSeriesCoefficient j q) - ∑ q ∈ range Q, singularSeriesCoefficient j q‖ ≤
      singularSeriesTail Q := by
  have hnorm := singularSeriesCoefficient_summable hMP j
  have hsum := hnorm.of_norm
  have hnQ : Summable (fun k => ‖singularSeriesCoefficient j (k+Q)‖) :=
    hnorm.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hmQ : Summable (fun k : ℕ => 1/((k+Q).totient : ℝ)^2) :=
    (summable_totient_reciprocal_sq hMP).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  rw [← hsum.sum_add_tsum_nat_add Q,add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hnQ).trans
    (hnQ.tsum_le_tsum (fun k => singularSeriesCoefficient_norm_le j (k+Q)) hmQ)

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoarseCoefficientVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative variation of the actual geometric coarse coefficients -/
namespace JointDickman
open Finset Classical

theorem primeCoarseCoefficient_sub (m B : ℕ)
    (K L : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (a b : Fin m) :
    primeCoarseCoefficient m B K a b-primeCoarseCoefficient m B L a b =
      primeCoarseCoefficient m B (fun i j => K i j-L i j) a b := by
  simp only [primeCoarseCoefficient,groupedKernelCoefficient,sum_sub_distrib,mul_sub]

theorem geometricWindowKernel_sub (m B : ℕ) (t L U : ℝ) (S : Finset ℤ)
    (V W : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (i j : Fin (channelFineCount m B)) :
    geometricWindowKernel m B t L U S V i j-geometricWindowKernel m B t L U S W i j =
      geometricWindowKernel m B t L U S (fun k i j => V k i j-W k i j) i j := by
  unfold geometricWindowKernel
  rw [← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem geometric_coarseCoefficient_bound {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D)
    (S : Finset ℤ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, |V k i j| ≤ D) (a b : Fin m) :
    |primeCoarseCoefficient m B (geometricWindowKernel m B t L U S V) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*D)*(U-L+2)) := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hwidth : 0 ≤ U-L+1 := by linarith
  have hoverlap : 0 ≤ (1+U-L)/t+1 := by
    apply add_nonneg _ zero_le_one
    exact div_nonneg (by linarith) ht.le
  have hM : 0 ≤ ((1+U-L)/t+1)*D := mul_nonneg hoverlap hD
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : -(1/10 : ℝ) ≤ 0))
  obtain ⟨hheight,hsupp⟩ := geometricWindowKernel_bounds hm hB ht hLU hD S V hV
  have hr := (fineGridKernel_schur (channelFineCount_pos hm hBpos) _ hBr hwidth hM hmesh hheight hsupp).1
  apply primeCoarseCoefficient_bound hm hBpos _ _ a b
  intro i
  convert hr i using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem geometric_coarseCoefficient_difference {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D)
    (S : Finset ℤ)
    (V W : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, i ∈ geometricHistogramWindow m B t L U k →
      j ∈ geometricHistogramWindow m B t L U k → |V k i j-W k i j| ≤ D)
    (a b : Fin m) :
    |primeCoarseCoefficient m B (geometricWindowKernel m B t L U S V) a b-
      primeCoarseCoefficient m B (geometricWindowKernel m B t L U S W) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*D)*(U-L+2)) := by
  let Z := fun k i j => if i ∈ geometricHistogramWindow m B t L U k ∧
    j ∈ geometricHistogramWindow m B t L U k then V k i j-W k i j else 0
  have hZ : ∀ k ∈ S, ∀ i j, |Z k i j| ≤ D := by
    intro k hk i j
    by_cases hh : i ∈ geometricHistogramWindow m B t L U k ∧ j ∈ geometricHistogramWindow m B t L U k
    · simpa [Z,hh] using hV k hk i j hh.1 hh.2
    · simpa [Z,hh] using hD
  rw [primeCoarseCoefficient_sub]
  have he : (fun i j => geometricWindowKernel m B t L U S V i j-
      geometricWindowKernel m B t L U S W i j) = geometricWindowKernel m B t L U S Z := by
    funext i j
    rw [geometricWindowKernel_sub]
    unfold geometricWindowKernel
    congr 1
    apply sum_congr rfl
    intro k _
    simp only [Z]
    split_ifs <;> rfl
  rw [he]
  exact geometric_coarseCoefficient_bound hm hB ht hLU hD S Z hZ a b

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplitudeParameterVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variation of coarse coefficients under changing box amplitudes -/
namespace JointDickman
open Finset Classical

theorem endpointSpatialWeight_amplitude_difference (m B : ℕ) (t β : ℝ)
    (d e : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {D M₁ M₂ M₀ : ℝ}
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℤ) (hd : |d k-e k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁)
    (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀)
    (i j : Fin (channelFineCount m B)) :
    |endpointSpatialWeight m B t β d w₁ w₂ w k i j-
      endpointSpatialWeight m B t β e w₁ w₂ w k i j| ≤ D*M₁*M₂*M₀ := by
  let x := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)
  let y := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) j)/Real.exp ((k : ℝ)*t)
  change |d k*w₁ x*w₂ y*w (β*x-β*y)-e k*w₁ x*w₂ y*w (β*x-β*y)| ≤ _
  rw [show d k*w₁ x*w₂ y*w (β*x-β*y)-e k*w₁ x*w₂ y*w (β*x-β*y) =
    (d k-e k)*w₁ x*w₂ y*w (β*x-β*y) by ring]
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul hd (hw₁ x) (abs_nonneg _) hD)
    (hw₂ y) (abs_nonneg _) (mul_nonneg hD hM₁)) (hw _) (abs_nonneg _)
    (mul_nonneg (mul_nonneg hD hM₁) hM₂)

theorem geometric_coarseCoefficient_amplitude_difference {m B : ℕ}
    (hm : 0 < m) (hB : 1 ≤ B) {t L U β D M₁ M₂ M₀ : ℝ}
    (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (hM₀ : 0 ≤ M₀)
    (S : Finset ℤ) (d e : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hd : ∀ k ∈ S, |d k-e k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁)
    (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀) (a b : Fin m) :
    |primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)) a b-
      primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β e w₁ w₂ w)) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*(D*M₁*M₂*M₀))*(U-L+2)) := by
  exact geometric_coarseCoefficient_difference hm hB ht hLU (by positivity) S _ _
    (fun k hk i j _ _ => endpointSpatialWeight_amplitude_difference m B t β d e w₁ w₂ w
      hD hM₁ hM₂ k (hd k hk) hw₁ hw₂ hw i j) a b

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLabels
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicative bin labels and real interpolation

The count in a finite prime bin includes multiplicity. Its additivity gives
complete multiplicativity of the uncentered labels. Centering is performed
only after evaluating a label; no multiplicativity is claimed for it.

A tensor product of finite Vandermonde inverses expresses every function of
bounded count vectors as a fixed finite linear combination of real,
nonnegative, 1-bounded multiplicative interpolants.
-/

namespace JointDickman

open Finset

section Labels

variable {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]

theorem binLabel_apply {n : ℕ} (hn : n ≠ 0) (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z n = ∏ i, z i ^ binCount (E i) n := by simp [binLabel, hn]

end Labels

section Bounds

variable {ι : Type*} [Fintype ι] (E : ι → Finset ℕ)

theorem norm_binLabel_eq_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {n : ℕ} (hn : n ≠ 0) : ‖binLabel E z n‖ = 1 := by
  simp [binLabel_apply hn, norm_prod, norm_pow, hz]

theorem norm_binLabel_le_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) :
    ‖binLabel E z n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  exact (norm_binLabel_eq_one E z hz hn).le

theorem norm_centered_binLabel_le_two (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (n : ℕ) : ‖binLabel E z n - μ‖ ≤ 2 := by
  calc
    _ ≤ ‖binLabel E z n‖ + ‖μ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_binLabel_le_one E z hz n) hμ
    _ = 2 := by norm_num

end Bounds

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FiniteConvolutionShift
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short translations of a finite convolution with small coefficient variation -/
namespace JointDickman
open Finset Classical

theorem finiteConvolution_step (K : ℕ → ℝ) (g : ℕ → ℂ) (N v : ℕ) :
    finiteConvolution K g (N+1) (v+1)-finiteConvolution K g (N+1) v =
      (K N : ℂ)*g (v+N+1)-(K 0 : ℂ)*g v+
        ∑ j ∈ range N, ((K j-K (j+1) : ℝ) : ℂ)*g (v+j+1) := by
  have h₁ : finiteConvolution K g (N+1) (v+1) =
      (∑ j ∈ range N, (K j : ℂ)*g (v+j+1))+(K N : ℂ)*g (v+N+1) := by
    simp [finiteConvolution,sum_range_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have h₂ : finiteConvolution K g (N+1) v =
      (∑ j ∈ range N, (K (j+1) : ℂ)*g (v+j+1))+(K 0 : ℂ)*g v := by
    rw [finiteConvolution,sum_range_succ']
    simp only [Nat.add_assoc,add_zero]
  rw [h₁,h₂]
  simp only [Complex.ofReal_sub,sub_mul,sum_sub_distrib]
  ring

theorem finiteConvolution_step_bound (K : ℕ → ℝ) (g : ℕ → ℂ) (N v : ℕ)
    {G : ℝ} (hG : ∀ n, ‖g n‖ ≤ G) :
    ‖finiteConvolution K g (N+1) (v+1)-finiteConvolution K g (N+1) v‖ ≤
      G*finiteCoefficientVariation K N := by
  rw [finiteConvolution_step]
  have hb (a : ℝ) (n : ℕ) : ‖(a : ℂ)*g n‖ ≤ |a| *G := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hG n) (abs_nonneg a)
  calc
    _ ≤ ‖(K N : ℂ)*g (v+N+1)-(K 0 : ℂ)*g v‖+
        ‖∑ j ∈ range N, ((K j-K (j+1) : ℝ) : ℂ)*g (v+j+1)‖ := norm_add_le _ _
    _ ≤ (|K N| *G+|K 0| *G)+∑ j ∈ range N, |K j-K (j+1)| *G := by
      apply add_le_add
      · exact (norm_sub_le _ _).trans (add_le_add (hb _ _) (hb _ _))
      · exact (norm_sum_le _ _).trans (sum_le_sum (fun j _ => hb _ _))
    _ = _ := by rw [← sum_mul]; unfold finiteCoefficientVariation; ring

theorem finiteConvolution_shift_bound (K : ℕ → ℝ) (g : ℕ → ℂ) (N v h : ℕ)
    {G : ℝ} (hG : ∀ n, ‖g n‖ ≤ G) :
    ‖finiteConvolution K g (N+1) (v+h)-finiteConvolution K g (N+1) v‖ ≤
      G*finiteCoefficientVariation K N*h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hs := finiteConvolution_step_bound K g N (v+h) hG
    calc
      _ ≤ ‖finiteConvolution K g (N+1) (v+h+1)-finiteConvolution K g (N+1) (v+h)‖+
          ‖finiteConvolution K g (N+1) (v+h)-finiteConvolution K g (N+1) v‖ := by
        convert norm_sub_le_norm_sub_add_norm_sub
          (finiteConvolution K g (N+1) (v+h+1))
          (finiteConvolution K g (N+1) (v+h)) (finiteConvolution K g (N+1) v) using 1
        all_goals try with_reducible_and_instances rfl
      _ ≤ G*finiteCoefficientVariation K N+G*finiteCoefficientVariation K N*h := add_le_add hs ih
      _ = _ := by push_cast <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PeriodicConvolutionSmoothing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothing a periodic lag factor along its residue class -/
namespace JointDickman
open Finset Classical

theorem norm_sub_average_le (A : ℂ) (B : ℕ → ℂ) {R : ℕ} (hR : 0 < R)
    {E : ℝ} (hE : ∀ h < R, ‖A-B h‖ ≤ E) :
    ‖A-(∑ h ∈ range R, B h)/(R : ℂ)‖ ≤ E := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have he : A-(∑ h ∈ range R, B h)/(R : ℂ) =
      (∑ h ∈ range R, (A-B h))/(R : ℂ) := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    field_simp
  rw [he,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ hRr).mpr
  calc
    _ ≤ ∑ h ∈ range R, ‖A-B h‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ range R, E := sum_le_sum (fun h hh => hE h (mem_range.mp hh))
    _ = _ := by simp <;> ring

theorem periodicConvolution_smoothing (K : ℕ → ℝ) (g : ℕ → ℂ)
    {q R : ℕ} (F : ZMod q → ℝ) (hR : 0 < R) (N v : ℕ)
    {G W : ℝ} (hG : ∀ n, ‖g n‖ ≤ G) (hF : ∀ r, |F r| ≤ W) :
    ‖(∑ j ∈ range (N+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*g (v+j))-
      ∑ j ∈ range (N+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*residueSmoothed g q R (v+j)‖ ≤
        W*G*finiteCoefficientVariation K N*(q*R : ℕ) := by
  let g' : ℕ → ℂ := fun n => (F ((n : ZMod q)-(v : ZMod q)) : ℂ)*g n
  have hG0 : 0 ≤ G := (norm_nonneg (g 0)).trans (hG 0)
  have hW0 : 0 ≤ W := (abs_nonneg (F 0)).trans (hF 0)
  have hg' n : ‖g' n‖ ≤ W*G := by
    dsimp only [g']
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (hF _) (hG n) (norm_nonneg _) hW0
  have hphase (j h : ℕ) :
      F (((v+q*(h+1)+j : ℕ) : ZMod q)-(v : ZMod q)) = F (j : ZMod q) := by
    congr 1
    push_cast
    simp
  have hbase (j : ℕ) : F (((v+j : ℕ) : ZMod q)-(v : ZMod q)) = F (j : ZMod q) := by
    congr 1
    push_cast
    ring
  let A : ℂ := ∑ j ∈ range (N+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*g (v+j)
  let V : ℕ → ℂ := fun h => ∑ j ∈ range (N+1),
    (K j : ℂ)*(F (j : ZMod q) : ℂ)*g (v+j+q*(h+1))
  have hshift (h : ℕ) (hh : h < R) :
      ‖A-V h‖ ≤ W*G*finiteCoefficientVariation K N*(q*R : ℕ) := by
    have hshiftBound := finiteConvolution_shift_bound K g' N v (q*(h+1)) hg'
    simp only [finiteConvolution,g',hphase,hbase] at hshiftBound
    have hV : (∑ j ∈ range (N+1), (K j : ℂ)*((F (j : ZMod q) : ℂ)*g (v+q*(h+1)+j))) = V h := by
      apply sum_congr rfl
      intro j _
      rw [show v+q*(h+1)+j = v+j+q*(h+1) by omega]
      ring
    simp only [hV] at hshiftBound
    have hA : (∑ j ∈ range (N+1), (K j : ℂ)*((F (j : ZMod q) : ℂ)*g (v+j))) = A := by
      dsimp only [A]
      apply sum_congr rfl
      intro j _
      ring
    rw [hA,norm_sub_rev] at hshiftBound
    apply hshiftBound.trans
    have hvar : 0 ≤ finiteCoefficientVariation K N := by
      unfold finiteCoefficientVariation
      positivity
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mul_le_mul_left q (show h+1 ≤ R by omega))
      (by positivity)
  have he : (∑ j ∈ range (N+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*residueSmoothed g q R (v+j)) =
      (∑ h ∈ range R, V h)/(R : ℂ) := by
    unfold residueSmoothed V
    simp only [← mul_div_assoc,mul_sum]
    rw [← sum_div,sum_comm]
  rw [he]
  exact norm_sub_average_le A V hR hshift

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseCenteredWeight
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform pointwise bound for centered coarse arithmetic features -/
namespace JointDickman
open Finset

theorem norm_centered_coarse_weight_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) {m : ℕ} (hm : 0 < m)
    (B : ℕ) (b : Fin m) (n : ℕ) :
    ‖(binLabel E ζ n-μ)*(primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b) n : ℂ)‖ ≤
      2/channelMesh m := by
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,mul_zero,norm_zero]
    exact div_nonneg (by norm_num) (channelMesh_pos hm).le
  · rw [norm_mul,primeSiteWeight_apply _ _ hn,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primeCoarseFeature_bounds hm b _).1]
    exact (mul_le_mul (norm_centered_binLabel_le_two E ζ hζ μ hμ n)
      (primeCoarseFeature_bounds hm b _).2 (primeCoarseFeature_bounds hm b _).1
      (by norm_num)).trans_eq (by ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CutBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real cut tests control complex label energies

This is the deterministic estimate (graph-cut-labels) in the manuscript.
It makes no independence assumption about the labels and the kernel.
-/

open scoped BigOperators ComplexConjugate

namespace JointDickman

theorem abs_cutSign (b : Bool) : |cutSign b| = 1 := by
  cases b <;> norm_num [cutSign]

/-- A linear test bounded for all sign vectors is bounded throughout the cube. -/
theorem linear_bound_of_signs {ι : Type*} [Fintype ι] (a : ι → ℝ) (C : ℝ)
    (hsign : ∀ s : ι → Bool, |∑ i, a i * cutSign (s i)| ≤ C)
    (f : ι → ℝ) (hf : ∀ i, |f i| ≤ 1) : |∑ i, a i * f i| ≤ C := by
  classical
  let s : ι → Bool := fun i => decide (0 ≤ a i)
  have heq : (∑ i, a i * cutSign (s i)) = ∑ i, |a i| := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ a i
    · simp [s, cutSign, hi, abs_of_nonneg hi]
    · simp [s, cutSign, hi, abs_of_neg (lt_of_not_ge hi)]
  have hsum : (∑ i, |a i|) ≤ C := by
    have h := hsign s
    rw [heq, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
    exact h
  calc
    |∑ i, a i * f i| ≤ ∑ i, |a i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)).trans_eq (mul_one _)
    _ ≤ C := hsum

/-- The two applications of the linear sign lemma give the exact extension
from the finite sign maximum to arbitrary real test coordinates in `[-1,1]`. -/
theorem realBilinear_bound_of_signs {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ s t : ι → Bool,
      |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤ C)
    (f g : ι → ℝ) (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |realBilinear K f g| ≤ C := by
  have hrow (u v : ι → ℝ) :
      realBilinear K u v = ∑ i, (∑ j, K i j * v j) * u i := by
    simp only [realBilinear, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcol (u v : ι → ℝ) :
      realBilinear K u v = ∑ j, (∑ i, K i j * u i) * v j := by
    simp only [realBilinear, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hs (s : ι → Bool) : |realBilinear K (fun i => cutSign (s i)) g| ≤ C := by
    rw [hcol]
    apply linear_bound_of_signs _ C _ g hg
    intro t
    rw [← hcol]
    exact hcut s t
  rw [hrow]
  apply linear_bound_of_signs _ C _ f hf
  intro s
  rw [← hrow]
  exact hs s

theorem realBilinear_rescale {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (f g : ι → ℝ) :
    realBilinear K f g =
      4 * realBilinear K (fun i => f i / 2) (fun i => g i / 2) := by
  simp only [realBilinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realBilinear_bound_two {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ f g : ι → ℝ, (∀ i, |f i| ≤ 1) → (∀ i, |g i| ≤ 1) →
      |realBilinear K f g| ≤ C)
    (f g : ι → ℝ) (hf : ∀ i, |f i| ≤ 2) (hg : ∀ i, |g i| ≤ 2) :
    |realBilinear K f g| ≤ 4 * C := by
  rw [realBilinear_rescale, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply hcut
  · intro i
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hf i]
  · intro i
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hg i]

theorem complexEnergy_re {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    (complexEnergy K z).re =
      realBilinear K (fun i => (z i).re) (fun i => (z i).re) +
      realBilinear K (fun i => (z i).im) (fun i => (z i).im) := by
  simp [complexEnergy, realBilinear, Complex.mul_re, Complex.mul_im,
    Finset.sum_add_distrib]

theorem complexEnergy_im {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    (complexEnergy K z).im =
      realBilinear K (fun i => (z i).re) (fun i => (z i).im) -
      realBilinear K (fun i => (z i).im) (fun i => (z i).re) := by
  simp [complexEnergy, realBilinear, Complex.mul_re, Complex.mul_im,
    Finset.sum_add_distrib, sub_eq_add_neg]

/-- The factor 16 is the one used when the centered labels have norm at most 2. -/
theorem complexEnergy_le_sixteen {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ f g : ι → ℝ, (∀ i, |f i| ≤ 1) → (∀ i, |g i| ≤ 1) →
      |realBilinear K f g| ≤ C)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    ‖complexEnergy K z‖ ≤ 16 * C := by
  have hre (i : ι) : |(z i).re| ≤ 2 := (Complex.abs_re_le_norm _).trans (hz i)
  have him (i : ι) : |(z i).im| ≤ 2 := (Complex.abs_im_le_norm _).trans (hz i)
  have hrr := realBilinear_bound_two K C hcut _ _ hre hre
  have hii := realBilinear_bound_two K C hcut _ _ him him
  have hri := realBilinear_bound_two K C hcut _ _ hre him
  have hir := realBilinear_bound_two K C hcut _ _ him hre
  calc
    ‖complexEnergy K z‖ ≤ |(complexEnergy K z).re| + |(complexEnergy K z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 16 * C := by
      rw [complexEnergy_re, complexEnergy_im]
      have ha := abs_add_le
        (realBilinear K (fun i => (z i).re) (fun i => (z i).re))
        (realBilinear K (fun i => (z i).im) (fun i => (z i).im))
      have hb := abs_sub
        (realBilinear K (fun i => (z i).re) (fun i => (z i).im))
        (realBilinear K (fun i => (z i).im) (fun i => (z i).re))
      linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointParameterVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lipschitz dependence of the spatial model on its lag parameter -/
namespace JointDickman
open Finset Classical

theorem histogramLocation_le {m B : ℕ} (hB : 0 < B)
    {t L U : ℝ} {k : ℤ} {i : Fin (channelFineCount m B)}
    (hi : i ∈ geometricHistogramWindow m B t L U k) :
    Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t) ≤ Real.exp U := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := (le_div_iff₀ hBr).mp (mem_filter.mp hi).2.1
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem endpointSpatialWeight_parameter_difference {m B : ℕ} (hB : 0 < B)
    {t L U D M₁ M₂ β γ : ℝ} (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {K : NNReal} (hw : LipschitzWith K w)
    (k : ℤ) (hd : |d k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂)
    (i j : Fin (channelFineCount m B))
    (hi : i ∈ geometricHistogramWindow m B t L U k)
    (hj : j ∈ geometricHistogramWindow m B t L U k) :
    |endpointSpatialWeight m B t β d w₁ w₂ w k i j-
      endpointSpatialWeight m B t γ d w₁ w₂ w k i j| ≤
      D*M₁*M₂*(K : ℝ)*Real.exp U*|β-γ| := by
  let x := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)
  let y := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) j)/Real.exp ((k : ℝ)*t)
  have hx0 : 0 < x := div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hy0 : 0 < y := div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hx : x ≤ Real.exp U := histogramLocation_le hB hi
  have hy : y ≤ Real.exp U := histogramLocation_le hB hj
  have hxy : |x-y| ≤ Real.exp U := abs_le.mpr ⟨by linarith,by linarith⟩
  have hl := hw.dist_le_mul (β*x-β*y) (γ*x-γ*y)
  rw [Real.dist_eq,Real.dist_eq,show β*x-β*y-(γ*x-γ*y) = (β-γ)*(x-y) by ring,abs_mul] at hl
  have hl' : |w (β*x-β*y)-w (γ*x-γ*y)| ≤ (K : ℝ)*|β-γ| *Real.exp U :=
    by
      have hh := hl.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxy (abs_nonneg _)) K.coe_nonneg)
      simpa only [mul_assoc] using hh
  have hc : |d k*w₁ x*w₂ y| ≤ D*M₁*M₂ := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul hd (hw₁ x) (abs_nonneg _) hD) (hw₂ y) (abs_nonneg _) (mul_nonneg hD hM₁)
  change |d k*w₁ x*w₂ y*w (β*x-β*y)-d k*w₁ x*w₂ y*w (γ*x-γ*y)| ≤ _
  rw [← mul_sub,abs_mul]
  have hh := mul_le_mul hc hl' (abs_nonneg _) (by positivity : 0 ≤ D*M₁*M₂)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring


theorem geometric_coarseCoefficient_parameter_difference {m B : ℕ}
    (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D M₁ M₂ β γ : ℝ} (ht : 0 < t) (hLU : L ≤ U)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (S : Finset ℤ) (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    {K : NNReal} (hw : LipschitzWith K w)
    (hd : ∀ k ∈ S, |d k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂)
    (a b : Fin m) :
    |primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)) a b-
      primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t γ d w₁ w₂ w)) a b| ≤
      (channelMesh m*(2*(((1+U-L)/t+1)*(D*M₁*M₂*(K : ℝ)*Real.exp U))*(U-L+2)))*|β-γ| := by
  have hh := geometric_coarseCoefficient_difference hm hB ht hLU
    (show 0 ≤ D*M₁*M₂*(K : ℝ)*Real.exp U*|β-γ| by positivity) S
    (endpointSpatialWeight m B t β d w₁ w₂ w)
    (endpointSpatialWeight m B t γ d w₁ w₂ w)
    (fun k hk i j hi hj => endpointSpatialWeight_parameter_difference (by omega)
      hD hM₁ hM₂ d w₁ w₂ w hw k (hd k hk) hw₁ hw₂ i j hi hj) a b
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorProductMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite divisor expansion and its mean bound -/

namespace JointDickman

open Finset

theorem primeProduct_dvd_iff (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (n : ℕ) :
    (∏ p ∈ D, p) ∣ n ↔ ∀ p ∈ D, p ∣ n := by
  refine ⟨fun h p hp => (dvd_prod_of_mem id hp).trans h, ?_⟩
  intro h
  by_cases hn : n = 0
  · simp [hn]
  have hsub : D ⊆ n.primeFactors := fun p hp => (hD p hp).mem_primeFactors (h p hp) hn
  exact (prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd n)

open Classical in
theorem divisor_product_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (n : ℕ) :
    (∏ p ∈ P, if p ∣ n then 1 + b p else 1) =
      ∑ D ∈ P.powerset, if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, b p else 0 := by
  have heq (p : ℕ) : (if p ∣ n then 1 + b p else 1) =
      1 + (if p ∣ n then b p else 0) := by split_ifs <;> simp
  simp_rw [heq]
  rw [prod_one_add]
  apply sum_congr rfl
  intro D hD
  rw [prod_ite_zero]
  simp only [primeProduct_dvd_iff D (fun p hp => hP p (mem_powerset.mp hD hp))]

open Classical in
theorem divisor_product_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (hb : ∀ p ∈ P, 0 ≤ b p) (U : ℕ) :
    (∑ n ∈ Ioc 0 U, ∏ p ∈ P, if p ∣ n then 1 + b p else 1) ≤
      (U : ℝ) * ∏ p ∈ P, (1 + b p / p) := by
  simp_rw [divisor_product_expansion P hP b]
  rw [sum_comm]
  calc
    _ = ∑ D ∈ P.powerset,
        ((U / (∏ p ∈ D, p) : ℕ) : ℝ) * ∏ p ∈ D, b p := by
      apply sum_congr rfl
      intro D _
      rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ D ∈ P.powerset, ((U : ℝ) / (∏ p ∈ D, p)) * ∏ p ∈ D, b p := by
      apply sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_right Nat.cast_div_le
      exact prod_nonneg (fun p hp => hb p (mem_powerset.mp hD hp))
    _ = (U : ℝ) * ∑ D ∈ P.powerset, ∏ p ∈ D, (b p / p) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro D _
      rw [prod_div_distrib, Nat.cast_prod]
      ring
    _ = _ := by rw [← prod_one_add]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorProductDifference
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing large-prime factors from a divisor product in mean -/
namespace JointDickman
open Finset Classical

theorem divisor_product_difference_mean {P Q : Finset ℕ} (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) (hb : ∀ p ∈ P, 0 ≤ b p) (U : ℕ) :
    (∑ n ∈ Ioc 0 U, ((∏ p ∈ P, if p ∣ n then 1+b p else 1)-
      ∏ p ∈ Q, if p ∣ n then 1+b p else 1)) ≤
      (U : ℝ)*((∏ p ∈ P, (1+b p/p))-(∏ p ∈ Q, (1+b p/p))) := by
  have hsets : Q.powerset ⊆ P.powerset := powerset_mono.mpr hQP
  simp_rw [divisor_product_expansion P hP b,
    divisor_product_expansion Q (fun p hp => hP p (hQP hp)) b,← sum_sdiff hsets,add_sub_cancel_right]
  rw [sum_comm]
  calc
    _ = ∑ D ∈ P.powerset \ Q.powerset,
        ((U/(∏ p ∈ D, p) : ℕ) : ℝ)*∏ p ∈ D, b p := by
      apply sum_congr rfl
      intro D _
      rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ D ∈ P.powerset \ Q.powerset,
        ((U : ℝ)/(∏ p ∈ D, p))*∏ p ∈ D, b p := by
      apply sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_right Nat.cast_div_le
      exact prod_nonneg (fun p hp => hb p (mem_powerset.mp (mem_sdiff.mp hD).1 hp))
    _ = (U : ℝ)*∑ D ∈ P.powerset \ Q.powerset, ∏ p ∈ D, b p/p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro D _
      rw [prod_div_distrib,Nat.cast_prod]
      ring
    _ = _ := by
      have hs := sum_sdiff hsets (f := fun D : Finset ℕ => ∏ p ∈ D, b p/p)
      rw [← prod_one_add,← prod_one_add] at hs
      congr 1
      linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteProductTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An exponential bound for tails of finite positive Euler products -/
namespace JointDickman
open Finset Classical

theorem prod_one_add_le_exp_sum {ι : Type*} (S : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ S, 0 ≤ b i) :
    (∏ i ∈ S, (1+b i)) ≤ Real.exp (∑ i ∈ S, b i) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    linarith [hb i hi]
  · intro i _
    simpa only [add_comm] using Real.add_one_le_exp (b i)

theorem exp_sub_one_le_exp_mul (x : ℝ) : Real.exp x-1 ≤ Real.exp x*x := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  nlinarith

theorem prod_one_add_difference_bound {ι : Type*} [DecidableEq ι]
    {P Q : Finset ι} (hQP : Q ⊆ P) (b : ι → ℝ) (hb : ∀ i ∈ P, 0 ≤ b i) :
    0 ≤ (∏ i ∈ P, (1+b i))-(∏ i ∈ Q, (1+b i)) ∧
    (∏ i ∈ P, (1+b i))-(∏ i ∈ Q, (1+b i)) ≤
      Real.exp (∑ i ∈ P, b i)*(∑ i ∈ P \ Q, b i) := by
  let R := P \ Q
  have hbQ i hi := hb i (hQP hi)
  have hbR i (hi : i ∈ R) := hb i (mem_sdiff.mp hi).1
  have hP0 : 0 ≤ ∏ i ∈ Q, (1+b i) := prod_nonneg (fun i hi => by linarith [hbQ i hi])
  have hR1 : 1 ≤ ∏ i ∈ R, (1+b i) := Finset.one_le_prod (fun i hi => by linarith [hbR i hi])
  have hid : (∏ i ∈ P, (1+b i))-(∏ i ∈ Q, (1+b i)) =
      (∏ i ∈ Q, (1+b i))*((∏ i ∈ R, (1+b i))-1) := by
    rw [← prod_sdiff hQP]
    dsimp only [R]
    ring
  rw [hid]
  refine ⟨mul_nonneg hP0 (sub_nonneg.mpr hR1),?_⟩
  have hprodQ := prod_one_add_le_exp_sum Q b hbQ
  have htail : (∏ i ∈ R, (1+b i))-1 ≤ Real.exp (∑ i ∈ R, b i)*(∑ i ∈ R, b i) :=
    (sub_le_sub_right (prod_one_add_le_exp_sum R b hbR) 1).trans (exp_sub_one_le_exp_mul _)
  have hh := mul_le_mul hprodQ htail (sub_nonneg.mpr hR1) (Real.exp_pos _).le
  refine hh.trans_eq ?_
  rw [← mul_assoc,← Real.exp_add]
  congr 1
  have hs : (∑ i ∈ Q, b i)+(∑ i ∈ R, b i) = ∑ i ∈ P, b i := by
    dsimp only [R]
    rw [add_comm,sum_sdiff hQP]
  rw [hs]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteWeightedSquare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite square bound for the smoothed coefficient sum -/
namespace JointDickman
open Finset

theorem finite_weighted_square_bound {ι : Type*} (S : Finset ι) (a b : ι → ℂ)
    {C : ℝ} (ha : ∀ i ∈ S, ‖a i‖ ≤ C) :
    ‖∑ i ∈ S, a i*b i‖^2 ≤ (S.card : ℝ)*C^2*∑ i ∈ S, ‖b i‖^2 := by
  have hs := norm_sum_le S (fun i => a i*b i)
  have hc := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖a i*b i‖)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hc
  apply ((pow_le_pow_left₀ (norm_nonneg _) hs 2).trans hc).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i hi) 2) (sq_nonneg _)

theorem finite_weighted_square_mean {ι κ : Type*} (I : Finset ι) (S : Finset κ)
    (a b : ι → κ → ℂ) {C X ε : ℝ} (hX : 0 < X)
    (ha : ∀ u ∈ I, ∀ j ∈ S, ‖a u j‖ ≤ C)
    (hb : ∀ j ∈ S, (1/X)*(∑ u ∈ I, ‖b u j‖^2) ≤ ε) :
    (1/X)*(∑ u ∈ I, ‖∑ j ∈ S, a u j*b u j‖^2) ≤ (S.card : ℝ)^2*C^2*ε := by
  calc
    _ ≤ (1/X)*(∑ u ∈ I, (S.card : ℝ)*C^2*∑ j ∈ S, ‖b u j‖^2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun u hu =>
        finite_weighted_square_bound S (a u) (b u) (ha u hu))) (by positivity)
    _ = (S.card : ℝ)*C^2*∑ j ∈ S, (1/X)*(∑ u ∈ I, ‖b u j‖^2) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro u _
      ring
    _ ≤ (S.card : ℝ)*C^2*∑ _j ∈ S, ε :=
      mul_le_mul_of_nonneg_left (sum_le_sum hb) (by positivity)
    _ = _ := by simp <;> ring

theorem norm_square_le_twice_difference (a b : ℂ) :
    ‖a‖^2 ≤ 2*‖a-b‖^2+2*‖b‖^2 := by
  have ht : ‖a‖ ≤ ‖a-b‖+‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a-b) b
  nlinarith [norm_nonneg a,norm_nonneg (a-b),norm_nonneg b,sq_nonneg (‖a-b‖-‖b‖)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularFactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded moments of the singular factor Σ(j) -/

namespace JointDickman

open Finset

theorem local_singular_power_bound {C : ℝ} (hC : 0 ≤ C) (r : ℕ)
    {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ (1 + C / p) ^ r - 1 ∧
      (1 + C / p) ^ r - 1 ≤ ((r : ℝ) * C * (1 + C) ^ (r - 1)) / p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hx : 1 ≤ 1 + C / p := le_add_of_nonneg_right (div_nonneg hC (Nat.cast_nonneg p))
  have hupper : 1 + C / p ≤ 1 + C := by
    linarith [div_le_self hC hp1]
  have hn : 0 ≤ (1 + C / p) ^ r - 1 := by
    exact sub_nonneg.mpr (one_le_pow₀ hx)
  refine ⟨hn, ?_⟩
  have h := abs_pow_sub_pow_le (1 + C / (p : ℝ)) 1 r
  simp only [one_pow, abs_of_nonneg hn, abs_of_nonneg (by positivity : 0 ≤ 1 + C / (p : ℝ)),
    abs_one, max_eq_left hx, add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ C / (p : ℝ))] at h
  calc
    _ ≤ C / (p : ℝ) * r * (1 + C / p) ^ (r - 1) := h
    _ ≤ C / (p : ℝ) * r * (1 + C) ^ (r - 1) := by gcongr
    _ = _ := by ring

open Classical in
theorem singularFactor_nat_moment {C : ℝ} (hC : 0 ≤ C) (r U : ℕ) :
    (∑ j ∈ Ioc 0 U, singularFactor C j ^ r) ≤
      Real.exp ((r : ℝ) * C * (1 + C) ^ (r - 1)) * U := by
  let P := Nat.primesLE U
  let b := fun p : ℕ => (1 + C / (p : ℝ)) ^ r - 1
  let K := (r : ℝ) * C * (1 + C) ^ (r - 1)
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hb (p : ℕ) (hp : p ∈ P) : 0 ≤ b p :=
    (local_singular_power_bound hC r (hP p hp).one_le).1
  have hbBound (p : ℕ) (hp : p ∈ P) : b p / p ≤ K / (p : ℝ) ^ 2 := by
    have h := div_le_div_of_nonneg_right
      (local_singular_power_bound hC r (hP p hp).one_le).2 (Nat.cast_nonneg p)
    simpa [b, K, div_div, pow_two] using h
  have hsum : (∑ p ∈ P, b p / p) ≤ K := by
    calc
      _ ≤ ∑ p ∈ P, K / (p : ℝ) ^ 2 := sum_le_sum hbBound
      _ = K * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by simp_rw [div_eq_mul_inv]; rw [mul_sum]; simp
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left
        (by
          simpa using sum_reciprocal_square_tail P (by norm_num : (1 : ℕ) ≠ 0)
            (fun p hp => (hP p hp).one_lt)) hK
      _ = K := mul_one _
  have hprod : (∏ p ∈ P, (1 + b p / p)) ≤ Real.exp K := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (b p / p) := Finset.prod_le_prod
        (fun p hp => by have := hb p hp; positivity)
        (fun p _ => by simpa [add_comm] using Real.add_one_le_exp (b p / p))
      _ = Real.exp (∑ p ∈ P, b p / p) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  have heq (j : ℕ) (hj : j ∈ Ioc 0 U) : singularFactor C j ^ r =
      ∏ p ∈ P, if p ∣ j then 1 + b p else 1 := by
    have hj0 : j ≠ 0 := Nat.ne_of_gt (mem_Ioc.mp hj).1
    have hfac : j.primeFactors = P.filter (fun p => p ∣ j) := by
      ext p
      simp only [P, mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
      constructor
      · rintro ⟨hp, hd, _⟩
        exact ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hd).trans (mem_Ioc.mp hj).2, hp⟩, hd⟩
      · rintro ⟨⟨_, hp⟩, hd⟩
        exact ⟨hp, hd, hj0⟩
    rw [singularFactor, hfac, ← prod_pow, prod_filter]
    apply prod_congr rfl
    intro p _
    simp [b]
  calc
    _ = ∑ j ∈ Ioc 0 U, ∏ p ∈ P, if p ∣ j then 1 + b p else 1 := sum_congr rfl heq
    _ ≤ (U : ℝ) * ∏ p ∈ P, (1 + b p / p) := divisor_product_mean P hP b hb U
    _ ≤ (U : ℝ) * Real.exp K := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg U)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularPrimeSets
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's regular prime sets and truncated weights -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem regularResidueWeight_nonneg (B L : ℕ) (τ C : ℝ) (S : Finset ℕ) :
    0 ≤ regularResidueWeight B L τ C S := by
  unfold regularResidueWeight residueBaseWeight
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _) (by positivity)
  · rfl

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TensorCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth separated factors for compact polynomial approximation -/

namespace JointDickman
open Finset
open scoped SchwartzMap

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingTransfer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative finite sampling transfer

The finite family consists of sampled column sequences and one sign per
sampled occurrence. Its cardinal is `(2 * N)^m`, including repeated columns.
The common bad event is paid once. Moment and tail obligations are explicit
mathematical hypotheses, not additional published inputs.
-/

open Finset
open scoped BigOperators
open JointDickman.PublishedInputs

namespace JointDickman

section ProbabilityTransfer

variable {Ω : Type*} [Fintype Ω]

theorem finiteExpectation_nonneg (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteExpectation w f :=
  sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

end ProbabilityTransfer

section CutFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kernelCutMaximum_le (K : ι → ι → ℝ) (C : ℝ)
    (hC : ∀ s t : ι → Bool,
      |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤ C) :
    kernelCutMaximum K ≤ C := by
  apply Finset.sup'_le
  intro st _
  exact hC st.1 st.2

theorem kernelCutMaximum_le_absolute_mass (K : ι → ι → ℝ) :
    kernelCutMaximum K ≤ ∑ i, ∑ j, |K i j| := by
  apply kernelCutMaximum_le
  intro s t
  unfold realBilinear
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  simp [abs_mul, abs_cutSign]

theorem kernelCutNorm_le_absolute_mass (K : ι → ι → ℝ) :
    kernelCutNorm K ≤ kernelAbsoluteMass K :=
  div_le_div_of_nonneg_right (kernelCutMaximum_le_absolute_mass K) (Nat.cast_nonneg _)

end CutFamily

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateRootKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent auxiliary-root weights for the actual candidate list -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

theorem independentPrimeSetMass_nonneg (B : ℕ) (R : (auxiliaryPrimes B).powerset) :
    0 ≤ independentPrimeSetMass B R := by
  apply bernoulliSubsetMass_nonneg (mem_powerset.mp R.property)
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).one_le
  exact ⟨by positivity, (div_le_one (by linarith : (0 : ℝ) < p)).mpr hp1⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IndependentRootMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded scalar root mean in the latent kernel -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

theorem independentRootMean_nonneg (B L : ℕ) (τ C : ℝ) :
    0 ≤ independentRootMean B L τ C :=
  finiteExpectation_nonneg _ _ (independentPrimeSetMass_nonneg B)
    (fun R => regularResidueWeight_nonneg B L τ C R.val)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPolynomialBounds
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

theorem weightedPolynomialTermKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) → ∀ x y,
        |weightedPolynomialTermKernel P d m B j c H T t S s r x y| ≤ C := by
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
  intro j T S hlog s hs r hr x y
  have hcoeff : ∀ k ∈ S, |(r k*(P.coeff d*(s k)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ R := by
    intro k hk
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog k hk]
    rw [abs_mul,abs_mul,abs_mul,abs_pow]
    apply mul_le_mul _ hden' (abs_nonneg _) (by positivity)
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hs k hk) (d 3)) (abs_nonneg (P.coeff d))
    exact (mul_le_mul (hr k hk) hp (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)) zero_le_one).trans_eq (one_mul _)
  exact geometric_primeCoarseKernel_bound hm hB ht (by norm_num) (by norm_num)
    hR hM₀ hM₁ hM₂ S _ _ _ _ hcoeff hw₀ hw₁ hw₂ x y

theorem weightedPolynomialPrimeKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (H : (Fin 4 →₀ ℕ) → ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) → ∀ x y,
        |weightedPolynomialPrimeKernel P m B j c H T t S s r x y| ≤ C := by
  choose C hC hbound using fun d => weightedPolynomialTermKernel_bounded hM hMP P d (hm d) (c d) (hc d) (H d) ht
  refine ⟨∑ d ∈ P.support, C d,sum_nonneg (fun d _ => hC d),?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun d _ => hbound d)] with B hb
  intro j T S hlog s hs r hr x y
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun d hd => hb d hd j T S hlog s hs r hr x y))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LagParameterVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized reciprocal lag is uniformly Lipschitz away from zero -/
namespace JointDickman

theorem reciprocal_lag_difference {T η x y : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hx : η*T ≤ x) (hy : η*T ≤ y) :
    |T/x-T/y| ≤ |x-y|/(η^2*T) := by
  have hx0 : 0 < x := (mul_pos hη hT).trans_le hx
  have hy0 : 0 < y := (mul_pos hη hT).trans_le hy
  have hxy : η^2*T^2 ≤ x*y := by
    have hh := mul_le_mul hx hy (mul_pos hη hT).le hx0.le
    nlinarith
  have he : T/x-T/y = T*(y-x)/(x*y) := by field_simp
  rw [he,abs_div,abs_mul,abs_of_pos hT,abs_of_pos (mul_pos hx0 hy0),abs_sub_comm y x]
  have hb := div_le_div_of_nonneg_left (mul_nonneg hT.le (abs_nonneg (x-y)))
    (by positivity : 0 < η^2*T^2) hxy
  refine hb.trans_eq ?_
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PolynomialTermLagVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lag variation of the polynomial model's finite coefficients -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem weightedPolynomialTermKernel_coefficients (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T t : ℝ) (S : Finset ℤ) (s r : ℤ → ℝ) (x y : auxiliaryPrimes B → Bool) :
    weightedPolynomialTermKernel P d m B j c H T t S s r x y =
      ∑ a, ∑ b, weightedTermCoefficient P d m B j c H T t S s r a b*
        primeCoarseFeature m B a x*primeCoarseFeature m B b y := rfl

theorem weightedTermCoefficient_lag_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j k : ℕ) (T : ℝ),
      0 < T → η*T ≤ j → η*T ≤ k → ∀ S : Finset ℤ,
      (∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ u ∈ S, |s u| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ u ∈ S, |r u| ≤ 1) → ∀ a b : Fin m,
      |weightedTermCoefficient P d m B j c H T t S s r a b-
        weightedTermCoefficient P d m B k c H T t S s r a b| ≤
        C*|(j : ℝ)-k|/T := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,D₀,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,D₁,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,D₂,_,hD₂,_,hd₂,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let K : NNReal := ⟨D₂,hD₂⟩
  have hLip : LipschitzWith K (tensorPowerFactor (d 2)) := by
    apply lipschitzWith_of_nnnorm_deriv_le (tensorPowerFactor (d 2)).differentiable
    intro x
    change ‖deriv (tensorPowerFactor (d 2)) x‖₊ ≤ K
    exact_mod_cast hd₂ x
  let R := |P.coeff d| *(3 : ℝ)^(d 3)*D
  let C₀ := channelMesh m*(2*(((1+Real.log (17/4)-Real.log (1/4))/t+1)*
    (R*M₀*M₁*(K : ℝ)*Real.exp (Real.log (17/4))))*(Real.log (17/4)-Real.log (1/4)+2))
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hR : 0 ≤ R := by positivity
  have hC₀ : 0 ≤ C₀ := by
    have hh : 0 ≤ (1+Real.log (17/4)-Real.log (1/4))/t+1 := by
      apply add_nonneg _ zero_le_one
      exact div_nonneg (by linarith) ht.le
    have hw : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
    dsimp only [C₀]
    exact mul_nonneg (channelMesh_pos hm).le
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hh (by positivity))) hw)
  refine ⟨C₀/η^2,by positivity,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j k T hT hj hk S hlog s hs r hr a b
  have hcoeff : ∀ u ∈ S, |(r u*(P.coeff d*(s u)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ R := by
    intro u hu
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog u hu]
    rw [abs_mul,abs_mul,abs_mul,abs_pow]
    apply mul_le_mul _ hden' (abs_nonneg _) (by positivity)
    have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hs u hu) (d 3)) (abs_nonneg (P.coeff d))
    exact (mul_le_mul (hr u hu) hp (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
      zero_le_one).trans_eq (one_mul _)
  have he := geometric_coarseCoefficient_parameter_difference hm hB ht hlogs hR hM₀ hM₁
    S (fun u => (r u*(P.coeff d*(s u)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B))
    (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2))
    (β := T/j) (γ := T/k) hLip hcoeff hw₀ hw₁ a b
  change |weightedTermCoefficient P d m B j c H T t S s r a b-
    weightedTermCoefficient P d m B k c H T t S s r a b| ≤ C₀*|T/j-T/k| at he
  have hb := he.trans (mul_le_mul_of_nonneg_left (reciprocal_lag_difference hT hη hj hk) hC₀)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PolynomialTermAmplitudeVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform variation of the polynomial model in its cutoff parameter -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem weightedTermCoefficient_parameter_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*t)/T)) →
      ∀ s₁ s₂ : ℤ → ℝ, (∀ u ∈ S, |s₁ u| ≤ 3) → (∀ u ∈ S, |s₂ u| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ u ∈ S, |r u| ≤ 1) → ∀ δ : ℝ, 0 ≤ δ →
      (∀ u ∈ S, |s₁ u-s₂ u| ≤ δ) → ∀ a b : Fin m,
      |weightedTermCoefficient P d m B j c H T t S s₁ r a b-
        weightedTermCoefficient P d m B j c H T t S s₂ r a b| ≤ C*δ := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,D₀,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,D₁,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,D₂,hM₂,_,hw₂,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let R := |P.coeff d| *(d 3 : ℝ)*(3 : ℝ)^(d 3-1)*D
  let C := channelMesh m*(2*(((1+Real.log (17/4)-Real.log (1/4))/t+1)*
    (R*M₀*M₁*M₂))*(Real.log (17/4)-Real.log (1/4)+2))
  have hR : 0 ≤ R := by positivity
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hC : 0 ≤ C := by
    have hh : 0 ≤ (1+Real.log (17/4)-Real.log (1/4))/t+1 := by
      apply add_nonneg _ zero_le_one
      exact div_nonneg (by linarith) ht.le
    have hw : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
    dsimp only [C]
    exact mul_nonneg (channelMesh_pos hm).le
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hh (by positivity))) hw)
  refine ⟨C,hC,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j T S hlog s₁ s₂ hs₁ hs₂ r hr δ hδ hdist a b
  have hcoeff : ∀ u ∈ S,
      |(r u*(P.coeff d*(s₁ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)-
        (r u*(P.coeff d*(s₂ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ R*δ := by
    intro u hu
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog u hu]
    have hp : |(s₁ u)^(d 3)-(s₂ u)^(d 3)| ≤ δ*(d 3 : ℝ)*(3 : ℝ)^(d 3-1) := by
      refine (abs_pow_sub_pow_le (s₁ u) (s₂ u) (d 3)).trans ?_
      gcongr
      · exact hdist u hu
      · exact max_le (hs₁ u hu) (hs₂ u hu)
    rw [show (r u*(P.coeff d*(s₁ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)-
        (r u*(P.coeff d*(s₂ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B) =
        r u*P.coeff d*((s₁ u)^(d 3)-(s₂ u)^(d 3))*
          coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B) by ring]
    simp only [abs_mul]
    have hh := mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_right (hr u hu) (abs_nonneg (P.coeff d))) hp
        (abs_nonneg _) (by positivity : 0 ≤ 1*|P.coeff d|)) hden'
      (abs_nonneg _) (by positivity : 0 ≤ (1*|P.coeff d|)*(δ*(d 3 : ℝ)*(3 : ℝ)^(d 3-1)))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [R]
    ring
  have hh := geometric_coarseCoefficient_amplitude_difference (β := T/j) hm hB ht hlogs
    (mul_nonneg hR hδ) hM₀ hM₁ hM₂ S _ _ _ _ _ hcoeff hw₀ hw₁ hw₂ a b
  change |weightedTermCoefficient P d m B j c H T t S s₁ r a b-
    weightedTermCoefficient P d m B j c H T t S s₂ r a b| ≤ _ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [C]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SingularSeriesMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary lag moments of the singular series -/

namespace JointDickman
open Finset

theorem totient_ratio_le_singularFactor {j : ℕ} (hj : 0 < j) :
    (j : ℝ)/j.totient ≤ singularFactor 24 j := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hp (p : ℕ) (h : p ∈ j.primeFactors) : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).two_le
  have hfactor (p : ℕ) (h : p ∈ j.primeFactors) : 0 < 1-1/(p : ℝ) := by
    have hpp := hp p h
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hprod : (0 : ℝ) < ∏ p ∈ j.primeFactors, (1-1/(p : ℝ)) := prod_pos hfactor
  have he : (j : ℝ)/j.totient = ∏ p ∈ j.primeFactors, (1-1/(p : ℝ))⁻¹ := by
    rw [totient_eq_prime_product_real,prod_inv_distrib]
    field_simp
  rw [he]
  apply Finset.prod_le_prod
  · intro p h
    exact inv_nonneg.mpr (hfactor p h).le
  · intro p h
    have hpp := hp p h
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (0 : ℝ) < p-1 := by linarith
    have heq : (1-1/(p : ℝ))⁻¹ = p/(p-1) := by field_simp
    rw [heq]
    apply (div_le_iff₀ hp1).mpr
    have hh : (1+24/(p : ℝ))*(p-1)-(p : ℝ) = (23*p-24)/p := by field_simp <;> ring
    have hnonneg : 0 ≤ (23*(p : ℝ)-24)/p := div_nonneg (by linarith) (by linarith)
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientProductTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A mean approximation of the totient ratio by finitely many prime factors -/
namespace JointDickman
open Finset Classical

theorem prime_totient_increment_bound {p : ℕ} (hp : p.Prime) :
    0 ≤ 1/((p : ℝ)-1) / p ∧ 1/((p : ℝ)-1) / p ≤ 2/(p : ℝ)^2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : 0 < (p : ℝ)-1 := by linarith
  constructor
  · positivity
  · rw [div_le_iff₀ hp0,div_le_iff₀ hp1]
    field_simp
    nlinarith

theorem prime_totient_increment_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, 1/((p : ℝ)-1)/p) ≤ 2 := by
  calc
    _ ≤ ∑ p ∈ P, 2/(p : ℝ)^2 :=
      sum_le_sum (fun p hp => (prime_totient_increment_bound (hP p hp)).2)
    _ = 2*∑ p ∈ P, 1/(p : ℝ)^2 := by rw [mul_sum]; congr 1; ext; ring
    _ ≤ 2*1 := mul_le_mul_of_nonneg_left
      (by
        simpa using (sum_reciprocal_square_tail P (show (1 : ℕ) ≠ 0 by omega)
          (fun p hp => (hP p hp).one_lt))) (by norm_num)
    _ = 2 := by ring

theorem prime_totient_increment_tail {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {Y : ℕ} (hY : 0 < Y) (hPY : ∀ p ∈ P, Y < p) :
    (∑ p ∈ P, 1/((p : ℝ)-1)/p) ≤ 2/(Y : ℝ) := by
  calc
    _ ≤ ∑ p ∈ P, 2/(p : ℝ)^2 :=
      sum_le_sum (fun p hp => (prime_totient_increment_bound (hP p hp)).2)
    _ = 2*∑ p ∈ P, 1/(p : ℝ)^2 := by rw [mul_sum]; congr 1; ext; ring
    _ ≤ 2*(1/(Y : ℝ)) := mul_le_mul_of_nonneg_left
      (sum_reciprocal_square_tail P (Nat.ne_of_gt hY) hPY) (by norm_num)
    _ = _ := by ring

theorem totientLocalProduct_eq_ratio {n Y : ℕ} (hn : 0 < n) (hnY : n ≤ Y) :
    totientLocalProduct Y n = (n : ℝ)/n.totient := by
  have hfac : n.primeFactors = (Nat.primesLE Y).filter (fun p => p ∣ n) := by
    ext p
    simp only [mem_filter,Nat.mem_primesLE,Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp,hd,_⟩
      exact ⟨⟨(Nat.le_of_dvd hn hd).trans hnY,hp⟩,hd⟩
    · rintro ⟨⟨_,hp⟩,hd⟩
      exact ⟨hp,hd,Nat.ne_of_gt hn⟩
  have he : (n : ℝ)/n.totient = ∏ p ∈ n.primeFactors, (1-1/(p : ℝ))⁻¹ := by
    rw [totient_eq_prime_product_real,prod_inv_distrib]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  rw [he,totientLocalProduct,← prod_filter,← hfac]
  apply prod_congr rfl
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
  field_simp
  ring

theorem totientLocalProduct_mono {Y Z : ℕ} (hYZ : Y ≤ Z) (n : ℕ) :
    totientLocalProduct Y n ≤ totientLocalProduct Z n := by
  unfold totientLocalProduct
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hYZ,
      (Nat.mem_primesLE.mp hp).2⟩
  · intro p hp
    split_ifs
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
      exact add_nonneg zero_le_one (div_nonneg zero_le_one (by linarith))
    · norm_num
  · intro p hp _
    split_ifs
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
      have : 0 ≤ 1/((p : ℝ)-1) := div_nonneg zero_le_one (by linarith)
      linarith
    · exact le_rfl

theorem totientLocalProduct_mean_error (Y U : ℕ) (hY : 0 < Y) :
    (∑ n ∈ Ioc 0 U, |(n : ℝ)/n.totient-totientLocalProduct Y n|) ≤
      (2*Real.exp 2)*(U : ℝ)/Y := by
  let P := Nat.primesLE (max U Y)
  let Q := Nat.primesLE Y
  have hQP : Q ⊆ P := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (le_max_right _ _),
      (Nat.mem_primesLE.mp hp).2⟩
  have hP p (hp : p ∈ P) := (Nat.mem_primesLE.mp hp).2
  have hb p (hp : p ∈ P) : 0 ≤ 1/((p : ℝ)-1) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact div_nonneg zero_le_one (by linarith)
  have hs : (∑ n ∈ Ioc 0 U, |(n : ℝ)/n.totient-totientLocalProduct Y n|) =
      ∑ n ∈ Ioc 0 U, ((∏ p ∈ P, if p ∣ n then 1+1/((p : ℝ)-1) else 1)-
        ∏ p ∈ Q, if p ∣ n then 1+1/((p : ℝ)-1) else 1) := by
    apply sum_congr rfl
    intro n hn
    have he := totientLocalProduct_eq_ratio (mem_Ioc.mp hn).1
      ((mem_Ioc.mp hn).2.trans (le_max_left U Y))
    rw [← he,abs_of_nonneg (sub_nonneg.mpr (totientLocalProduct_mono (le_max_right U Y) n))]
    rfl
  rw [hs]
  have hdiff := (prod_one_add_difference_bound hQP
    (fun p : ℕ => 1/((p : ℝ)-1)/p)
    (fun p hp => (prime_totient_increment_bound (hP p hp)).1)).2
  have htail := prime_totient_increment_tail
    (fun p (hp : p ∈ P \ Q) => hP p (mem_sdiff.mp hp).1) hY (by
      intro p hp
      have hpp := hP p (mem_sdiff.mp hp).1
      have hn := (mem_sdiff.mp hp).2
      simp only [Q,Nat.mem_primesLE,not_and] at hn
      exact Nat.lt_of_not_ge (fun h => hn h hpp))
  have hsum := prime_totient_increment_sum P hP
  calc
    _ ≤ (U : ℝ)*((∏ p ∈ P, (1+(1/((p : ℝ)-1))/p))-
        ∏ p ∈ Q, (1+(1/((p : ℝ)-1))/p)) :=
      divisor_product_difference_mean hQP hP (fun p => 1/((p : ℝ)-1)) hb U
    _ ≤ (U : ℝ)*(Real.exp 2*(2/(Y : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg U)
      exact hdiff.trans (mul_le_mul (Real.exp_le_exp.mpr hsum) htail
        (sum_nonneg (fun p hp => (prime_totient_increment_bound (hP p (mem_sdiff.mp hp).1)).1))
        (Real.exp_pos 2).le)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SingularSeriesPeriodic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A periodic finite-factor approximation to the lag singular series -/
namespace JointDickman
open Finset Classical

theorem totientLocalProduct_modEq {Y m n : ℕ}
    (h : m ≡ n [MOD Y.factorial]) : totientLocalProduct Y m = totientLocalProduct Y n := by
  apply prod_congr rfl
  intro p hp
  have hpY := Nat.mem_primesLE.mp hp
  have hd := h.dvd_iff (Nat.dvd_factorial hpY.2.pos hpY.1)
  simp only [hd]

theorem singularSeriesCoefficient_modEq {Q m n : ℕ}
    (h : m ≡ n [MOD Q.factorial]) {q : ℕ} (hq : q < Q) :
    singularSeriesCoefficient m q = singularSeriesCoefficient n q := by
  by_cases hq0 : q = 0
  · simp [hq0,singularSeriesCoefficient]
  have hqP : q ∣ Q.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hq0) hq.le
  have hh := (h.of_dvd hqP).gcd_eq
  have hc : q.Coprime m ↔ q.Coprime n := by
    change Nat.gcd q m = 1 ↔ Nat.gcd q n = 1
    rw [Nat.gcd_comm q m,Nat.gcd_comm q n,hh]
  simp only [singularSeriesCoefficient,hc]

theorem periodicSingularSeries_modEq (Y Q : ℕ) {m n : ℕ}
    (h : m ≡ n [MOD (max Y Q).factorial]) :
    periodicSingularSeries Y Q m = periodicSingularSeries Y Q n := by
  have hY := h.of_dvd (Nat.factorial_dvd_factorial (le_max_left Y Q))
  have hQ := h.of_dvd (Nat.factorial_dvd_factorial (le_max_right Y Q))
  unfold periodicSingularSeries
  rw [totientLocalProduct_modEq hY]
  congr 1
  exact sum_congr rfl (fun q hq => singularSeriesCoefficient_modEq hQ (mem_range.mp hq))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularSeriesApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodic approximation of the singular series in arithmetic mean -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem totientSquareSum_nonneg : 0 ≤ totientSquareSum :=
  tsum_nonneg (fun _ => by positivity)

theorem singularSeries_partial_abs_bound
    (hMP : PublishedInputs.PrimeProductMertensInput) (n Q : ℕ) :
    |∑ q ∈ range Q, singularSeriesCoefficient n q| ≤ totientSquareSum := by
  calc
    _ ≤ ∑ q ∈ range Q, |singularSeriesCoefficient n q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ range Q, 1/(q.totient : ℝ)^2 := sum_le_sum (fun q _ => by
      simpa only [Real.norm_eq_abs] using singularSeriesCoefficient_norm_le n q)
    _ ≤ totientSquareSum := (summable_totient_reciprocal_sq hMP).sum_le_tsum _
      (fun _ _ => by positivity)

theorem singularSeries_periodic_error (hMP : PublishedInputs.PrimeProductMertensInput)
    (Y Q n : ℕ) :
    |singularSeries n-periodicSingularSeries Y Q n| ≤
      ((n : ℝ)/n.totient)*singularSeriesTail Q +
        |(n : ℝ)/n.totient-totientLocalProduct Y n| *totientSquareSum := by
  let r : ℝ := (n : ℝ)/n.totient
  let a : ℝ := ∑' q, singularSeriesCoefficient n q
  let b : ℝ := ∑ q ∈ range Q, singularSeriesCoefficient n q
  have hr : 0 ≤ r := by dsimp [r] <;> positivity
  have ht : |a-b| ≤ singularSeriesTail Q := by
    simpa only [Real.norm_eq_abs] using singularSeries_tail_bound hMP n Q
  change |r*a-totientLocalProduct Y n*b| ≤ _
  calc
    _ = |r*(a-b)+(r-totientLocalProduct Y n)*b| := by congr 1; ring
    _ ≤ |r*(a-b)|+|(r-totientLocalProduct Y n)*b| := abs_add_le _ _
    _ = r*|a-b|+|r-totientLocalProduct Y n| *|b| := by rw [abs_mul,abs_mul,abs_of_nonneg hr]
    _ ≤ r*singularSeriesTail Q+|r-totientLocalProduct Y n| *totientSquareSum :=
      add_le_add (mul_le_mul_of_nonneg_left ht hr)
        (mul_le_mul_of_nonneg_left (singularSeries_partial_abs_bound hMP n Q) (abs_nonneg _))

theorem totient_ratio_mean_bound (U : ℕ) :
    (∑ n ∈ Ioc 0 U, (n : ℝ)/n.totient) ≤ Real.exp 24*U := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 U, singularFactor 24 n := sum_le_sum (fun n hn =>
      totient_ratio_le_singularFactor (mem_Ioc.mp hn).1)
    _ ≤ Real.exp 24*U := by
      simpa using singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 U

theorem singularSeries_periodic_mean_error
    (hMP : PublishedInputs.PrimeProductMertensInput) (Y Q U : ℕ) (hY : 0 < Y) :
    (∑ n ∈ Ioc 0 U, |singularSeries n-periodicSingularSeries Y Q n|) ≤
      (Real.exp 24*singularSeriesTail Q+(2*Real.exp 2*totientSquareSum)/(Y : ℝ))*U := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 U, (((n : ℝ)/n.totient)*singularSeriesTail Q+
        |(n : ℝ)/n.totient-totientLocalProduct Y n| *totientSquareSum) :=
      sum_le_sum (fun n _ => singularSeries_periodic_error hMP Y Q n)
    _ = (∑ n ∈ Ioc 0 U, (n : ℝ)/n.totient)*singularSeriesTail Q+
        (∑ n ∈ Ioc 0 U, |(n : ℝ)/n.totient-totientLocalProduct Y n|)*totientSquareSum := by
      rw [sum_add_distrib,sum_mul,sum_mul]
    _ ≤ (Real.exp 24*U)*singularSeriesTail Q+
        ((2*Real.exp 2)*(U : ℝ)/Y)*totientSquareSum :=
      add_le_add (mul_le_mul_of_nonneg_right (totient_ratio_mean_bound U)
        (singularSeriesTail_nonneg Q))
        (mul_le_mul_of_nonneg_right (totientLocalProduct_mean_error Y U hY) totientSquareSum_nonneg)
    _ = _ := by ring

/-- The finite period is fixed before the averaging length. -/
theorem singularSeries_periodic_approximation
    (hMP : PublishedInputs.PrimeProductMertensInput) {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℕ) (_ : NeZero q) (F : ZMod q → ℝ),
      ∀ U : ℕ, (∑ n ∈ Ioc 0 U, |singularSeries n-F (n : ZMod q)|) ≤ ε*U := by
  have hlim : Tendsto (fun N : ℕ => Real.exp 24*singularSeriesTail N+
      (2*Real.exp 2*totientSquareSum)/(N : ℝ)) atTop (𝓝 0) := by
    simpa using (singularSeriesTail_tendsto_zero.const_mul (Real.exp 24)).add
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2*Real.exp 2*totientSquareSum))
  obtain ⟨N,hN,hsmall⟩ := (eventually_ge_atTop 1 |>.and
    (hlim.eventually (eventually_lt_nhds hε))).exists
  let q := N.factorial
  have hq : NeZero q := ⟨Nat.factorial_ne_zero N⟩
  let := hq
  refine ⟨q,hq,fun r => periodicSingularSeries N N r.val,?_⟩
  intro U
  have he (n : ℕ) : periodicSingularSeries N N (n : ZMod q).val =
      periodicSingularSeries N N n := by
    apply periodicSingularSeries_modEq
    simpa only [max_self,ZMod.val_natCast] using Nat.mod_modEq n q
  simp_rw [he]
  exact (singularSeries_periodic_mean_error hMP N N U (by omega)).trans
    (mul_le_mul_of_nonneg_right hsmall.le (Nat.cast_nonneg U))

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCoefficientRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite coefficients of the actual counting model and their regularity -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem countingPrimeKernel_coefficients (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) (x y : auxiliaryPrimes B → Bool) :
    countingPrimeKernel P m B j c H T σ x y =
      ∑ d ∈ P.support, ∑ a, ∑ b, countingTermCoefficient P d (m d) B j (c d) (H d) T σ a b*
        primeCoarseFeature (m d) B a x*primeCoarseFeature (m d) B b y := by
  unfold countingPrimeKernel weightedPolynomialPrimeKernel
  apply sum_congr rfl
  intro d _
  rw [weightedPolynomialTermKernel_coefficients]
  rfl

theorem countingTermCoefficient_regular
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j k : ℕ) (T σ σ' : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j → η*T ≤ k →
      |σ| ≤ 3 → |σ'| ≤ 3 → ∀ a b : Fin m,
      |countingTermCoefficient P d m B j c H T σ a b-
        countingTermCoefficient P d m B k c H T σ' a b| ≤ C*(|(j : ℝ)-k|/T+|σ-σ'|) := by
  obtain ⟨C₁,hC₁,hLag⟩ := weightedTermCoefficient_lag_variation hM hMP P d hm c hc H
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hη
  obtain ⟨C₂,hC₂,hAmp⟩ := weightedTermCoefficient_parameter_variation hM hMP P d hm c hc H
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨C₁+C₂,add_nonneg hC₁ hC₂,?_⟩
  filter_upwards [hLag,hAmp,eventually_ge_atTop 30] with B hLag hAmp hB
  intro j k T σ σ' hT hlog hj hk hσ hσ' a b
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  let r := fun u : ℤ => amplificationBump (Real.log (Real.exp ((u : ℝ)*Real.log 2)/T)/B)
  have hS : ∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*Real.log 2)/T) := by
    intro u hu
    exact (((dyadic_scale_window hB hT hlog).2.1 u hu).2).1
  have hr : ∀ u ∈ S, |r u| ≤ 1 := by
    intro u _
    rw [abs_of_nonneg (amplificationBump_bounds _).1]
    exact (amplificationBump_bounds _).2
  have hl := hLag j k T (lt_of_lt_of_le zero_lt_one hT) hj hk S hS (fun _ => σ)
    (fun _ _ => hσ) r hr a b
  have ha := hAmp k T S hS (fun _ => σ) (fun _ => σ') (fun _ _ => hσ) (fun _ _ => hσ')
    r hr |σ-σ'| (abs_nonneg _) (fun _ _ => le_rfl) a b
  change |countingTermCoefficient P d m B j c H T σ a b-
    countingTermCoefficient P d m B k c H T σ a b| ≤ _ at hl
  change |countingTermCoefficient P d m B k c H T σ a b-
    countingTermCoefficient P d m B k c H T σ' a b| ≤ _ at ha
  have ht := (abs_sub_le (countingTermCoefficient P d m B j c H T σ a b)
    (countingTermCoefficient P d m B k c H T σ a b)
    (countingTermCoefficient P d m B k c H T σ' a b)).trans (add_le_add hl ha)
  apply ht.trans
  rw [mul_div_assoc]
  have hnn : 0 ≤ |(j : ℝ)-k|/T := div_nonneg (abs_nonneg _) (by linarith)
  nlinarith [mul_nonneg hC₁ (abs_nonneg (σ-σ')),mul_nonneg hC₂ hnn]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TermCoefficientBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform boundedness of the actual finite model coefficients -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem weightedTermCoefficient_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) → ∀ a b : Fin m,
        |weightedTermCoefficient P d m B j c H T t S s r a b| ≤ C := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,_,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,_,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,_,hM₂,_,hw₂,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let R := |P.coeff d| *(3 : ℝ)^(d 3)*D
  let C := channelMesh m*(2*((((1+Real.log (17/4)-Real.log (1/4))/t+1)*(R*M₀*M₁*M₂)))*
    (Real.log (17/4)-Real.log (1/4)+2))
  have hR : 0 ≤ R := by positivity
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hw : 0 ≤ 1+Real.log (17/4)-Real.log (1/4) := by linarith
  have hw' : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
  have hmesh := channelMesh_pos hm
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j T S hlog s hs r hr a b
  have hcoeff : ∀ k ∈ S, |(r k*(P.coeff d*(s k)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ R := by
    intro k hk
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog k hk]
    rw [abs_mul,abs_mul,abs_mul,abs_pow]
    apply mul_le_mul _ hden' (abs_nonneg _) (by positivity)
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hs k hk) (d 3)) (abs_nonneg (P.coeff d))
    exact (mul_le_mul (hr k hk) hp (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)) zero_le_one).trans_eq (one_mul _)
  apply geometric_coarseCoefficient_bound hm hB ht hlogs (by positivity) S _ _ a b
  exact endpointSpatialWeight_bound m B t (T/j) S _ _ _ _ hR hM₀ hM₁ hcoeff hw₀ hw₁ hw₂

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_NormalizedLagCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity of the lag coefficients after division by the lag -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem normalized_coefficient_difference {T η x y a b A L : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hx : η*T ≤ x) (hy : η*T ≤ y)
    (hb : |b| ≤ A)
    (hab : |a-b| ≤ L*|x-y|/T) :
    |(T/x)*a-(T/y)*b| ≤ (L/η+A/η^2)*|x-y|/T := by
  have hx0 : 0 < x := (mul_pos hη hT).trans_le hx
  have ht : |T/x| ≤ 1/η := by
    rw [abs_of_pos (div_pos hT hx0)]
    convert div_le_div_of_nonneg_left hT.le (mul_pos hη hT) hx using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have hh := reciprocal_lag_difference hT hη hx hy
  calc
    _ = |(T/x)*(a-b)+(T/x-T/y)*b| := by congr 1; ring
    _ ≤ |(T/x)*(a-b)|+|(T/x-T/y)*b| := abs_add_le _ _
    _ = |T/x| *|a-b|+|T/x-T/y| *|b| := by rw [abs_mul,abs_mul]
    _ ≤ (1/η)*(L*|x-y|/T)+(|x-y|/(η^2*T))*A := by
      exact add_le_add (mul_le_mul ht hab (abs_nonneg _) (by positivity))
        (mul_le_mul hh hb (abs_nonneg _) (by positivity))
    _ = _ := by ring

theorem countingTermCoefficient_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T σ : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → |σ| ≤ 3 → ∀ a b : Fin m,
      |countingTermCoefficient P d m B j c H T σ a b| ≤ A := by
  obtain ⟨A,hA,hbound⟩ := weightedTermCoefficient_bounded hM hMP P d hm c hc H
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨A,hA,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 30] with B hbound hB
  intro j T σ hT hlog hσ a b
  apply hbound j T _
  · intro k hk
    exact (((dyadic_scale_window hB hT hlog).2.1 k hk).2).1
  · exact fun _ _ => hσ
  · intro k _
    rw [abs_of_nonneg (amplificationBump_bounds _).1]
    exact (amplificationBump_bounds _).2

theorem counting_normalized_coefficient_regular
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ᶠ B : ℕ in atTop, ∀ (j k : ℕ) (T σ : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j → η*T ≤ k → |σ| ≤ 3 →
      ∀ a b : Fin m,
        |(T/j)*countingTermCoefficient P d m B j c H T σ a b| ≤ A ∧
        |(T/j)*countingTermCoefficient P d m B j c H T σ a b-
          (T/k)*countingTermCoefficient P d m B k c H T σ a b| ≤ L*|(j : ℝ)-k|/T := by
  obtain ⟨A,hA,hbound⟩ := countingTermCoefficient_bounded hM hMP P d hm c hc H
  obtain ⟨L,hL,hreg⟩ := countingTermCoefficient_regular hM hMP P d hm c hc H hη
  refine ⟨A/η,L/η+A/η^2,by positivity,by positivity,?_⟩
  filter_upwards [hbound,hreg] with B hbound hreg
  intro j k T σ hT hlog hj hk hσ a b
  have hT0 : 0 < T := by linarith
  have hj0 : (0 : ℝ) < j := (mul_pos hη hT0).trans_le hj
  have hratio : T/(j : ℝ) ≤ 1/η := by
    convert div_le_div_of_nonneg_left hT0.le (mul_pos hη hT0) hj using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  constructor
  · rw [abs_mul,abs_of_pos (div_pos hT0 hj0)]
    exact (mul_le_mul hratio (hbound j T σ hT hlog hσ a b) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  · apply normalized_coefficient_difference hT0 hη hj hk (hbound k T σ hT hlog hσ a b)
    simpa [mul_div_assoc] using hreg j k T σ σ hT hlog hj hk hσ hσ a b

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TruncatedUpperVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lag variation for a truncated row of the finite block -/
namespace JointDickman
open Finset Classical

theorem cutLagWeight_upper_variation (H U T : ℕ) (w : ℕ → ℝ) {A L : ℝ}
    (hT : 0 < T) (hU : 0 < U) (hUT : U ≤ T) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hw : ∀ j, H < j → j < U → |w j| ≤ A/(T : ℝ))
    (hd : ∀ j, H < j → j+1 < U → |w j-w (j+1)| ≤ L/(T : ℝ)^2) :
    finiteCoefficientVariation (cutLagWeight H U w) T ≤ (2*A+L)/T := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hstep (j : ℕ) :
      |cutLagWeight H U w j-cutLagWeight H U w (j+1)| ≤
        L/(T : ℝ)^2+(if j=H then A/(T : ℝ) else 0)+
          (if j+1=U then A/(T : ℝ) else 0) := by
    have hleft : 0 ≤ (if j=H then A/(T : ℝ) else 0) := by positivity
    have hright : 0 ≤ (if j+1=U then A/(T : ℝ) else 0) := by positivity
    have hder : 0 ≤ L/(T : ℝ)^2 := by positivity
    unfold cutLagWeight
    by_cases hj : H < j ∧ j < U <;> by_cases hj' : H < j+1 ∧ j+1 < U
    · rw [ite_eq_left hj,ite_eq_left hj']
      exact (hd j hj.1 hj'.2).trans (by linarith)
    · rw [ite_eq_left hj,ite_eq_right hj',sub_zero]
      have he : j+1=U := by omega
      rw [ite_eq_left he]
      exact (hw j hj.1 hj.2).trans (by linarith)
    · rw [ite_eq_right hj,ite_eq_left hj',zero_sub,abs_neg]
      have he : j=H := by omega
      rw [ite_eq_left he]
      exact (hw (j+1) hj'.1 hj'.2).trans (by linarith)
    · rw [ite_eq_right hj,ite_eq_right hj',sub_self,abs_zero]
      positivity
  have hsumH : (∑ j ∈ range T, if j=H then A/(T : ℝ) else 0) ≤ A/T := by
    rw [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hsumT : (∑ j ∈ range T, if j+1=U then A/(T : ℝ) else 0) ≤ A/T := by
    have he (j : ℕ) : j+1=U ↔ j=U-1 := by omega
    simp only [he,sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hsum := (sum_le_sum (fun j (_ : j ∈ range T) => hstep j)).trans
    (show (∑ j ∈ range T, (L/(T : ℝ)^2+(if j=H then A/(T : ℝ) else 0)+
      (if j+1=U then A/(T : ℝ) else 0))) ≤ (T : ℝ)*(L/(T : ℝ)^2)+A/T+A/T by
        rw [sum_add_distrib,sum_add_distrib,sum_const,card_range,nsmul_eq_mul]
        exact add_le_add (add_le_add le_rfl hsumH) hsumT)
  have h0 : cutLagWeight H U w 0 = 0 := by simp [cutLagWeight]
  have hTT : cutLagWeight H U w T = 0 := by simp [cutLagWeight,not_lt_of_ge hUT]
  rw [finiteCoefficientVariation,h0,hTT,abs_zero,zero_add,zero_add]
  apply hsum.trans_eq
  field_simp
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingUpperVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting coefficient bounds for truncated block rows -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem counting_lag_upper_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (D : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H U : ℕ) (σ : ℝ),
      0 < T → 0 < U → U ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ H → |σ| ≤ 3 → ∀ a b : Fin m,
      finiteCoefficientVariation (cutLagWeight H U
        (fun j => countingTermCoefficient P d m B j c D T σ a b/(j : ℝ))) T ≤ C/T := by
  obtain ⟨A,L,hA,hL,hreg⟩ := counting_normalized_coefficient_regular hM hMP P d hm c hc D hη
  refine ⟨2*A+L,by positivity,?_⟩
  filter_upwards [hreg] with B hB
  intro T H U σ hT hU hUT hlog hH hσ a b
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  let f := fun j => countingTermCoefficient P d m B j c D T σ a b
  have he (j : ℕ) : f j/(j : ℝ) = ((T : ℝ)/j*f j)/T := by field_simp
  have hj (j : ℕ) (hh : H < j) : η*(T : ℝ) ≤ j := hH.trans (by exact_mod_cast hh.le)
  apply cutLagWeight_upper_variation H U T _ hT hU hUT hA hL
  · intro j hh _
    rw [he,abs_div,abs_of_pos hTr]
    exact div_le_div_of_nonneg_right (hB j j T σ hT1 hlog (hj j hh) (hj j hh) hσ a b).1 hTr.le
  · intro j hh _
    rw [he,he,← sub_div,abs_div,abs_of_pos hTr]
    have hj' : η*(T : ℝ) ≤ (j+1 : ℕ) := (hj j hh).trans (by norm_cast; omega)
    have hv := (hB j (j+1) T σ hT1 hlog (hj j hh) hj' hσ a b).2
    have habs : |(j : ℝ)-(j+1 : ℕ)| = 1 := by push_cast; ring_nf; norm_num
    rw [habs,mul_one] at hv
    exact (div_le_div_of_nonneg_right hv hTr.le).trans_eq (by ring)

theorem counting_lag_upper_weight_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (D : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H U : ℕ) (σ : ℝ),
      0 < T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ H → |σ| ≤ 3 → ∀ (a b : Fin m) (j : ℕ),
      |cutLagWeight H U (fun k => countingTermCoefficient P d m B k c D T σ a b/(k : ℝ)) j| ≤ A/T := by
  obtain ⟨A,hA,hbound⟩ := countingTermCoefficient_bounded hM hMP P d hm c hc D
  refine ⟨A/η,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro T H U σ hT hlog hH hσ a b j
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  unfold cutLagWeight
  split_ifs with hj
  · have hjr : η*(T : ℝ) ≤ j := hH.trans (by exact_mod_cast hj.1.le)
    have hj0 : (0 : ℝ) < j := (mul_pos hη hTr).trans_le hjr
    rw [abs_div,abs_of_pos hj0]
    calc
      _ ≤ A/(j : ℝ) := div_le_div_of_nonneg_right (hB j T σ hT1 hlog hσ a b) hj0.le
      _ ≤ A/(η*T) := div_le_div_of_nonneg_left hA (mul_pos hη hTr) hjr
      _ = _ := by ring
  · rw [abs_zero]
    positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CountingUpperSmoothing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short progression smoothing of the actual counting coefficient -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem counting_lag_upper_smoothing
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (D : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H U : ℕ) (σ : ℝ),
      0 < T → 0 < U → U ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ H → |σ| ≤ 3 →
      ∀ (a b : Fin m) (q R v : ℕ) (F : ZMod q → ℝ) (g : ℕ → ℂ) (G W : ℝ),
        0 < R → (∀ n, ‖g n‖ ≤ G) → (∀ r, |F r| ≤ W) →
      let K := cutLagWeight H U (fun j => countingTermCoefficient P d m B j c D T σ a b/(j : ℝ))
      ‖(∑ j ∈ range (T+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*g (v+j))-
        ∑ j ∈ range (T+1), (K j : ℂ)*(F (j : ZMod q) : ℂ)*residueSmoothed g q R (v+j)‖ ≤
          (W*G*C)*(q*R : ℕ)/T := by
  obtain ⟨C,hC,hvar⟩ := counting_lag_upper_variation hM hMP P d hm c hc D hη
  refine ⟨C,hC,?_⟩
  filter_upwards [hvar] with B hB
  intro T H U σ hT hU hUT hlog hH hσ a b q R v F g G W hR hG hF K
  have hG0 : 0 ≤ G := (norm_nonneg (g 0)).trans (hG 0)
  have hW0 : 0 ≤ W := (abs_nonneg (F 0)).trans (hF 0)
  apply (periodicConvolution_smoothing K g F hR T v hG hF).trans
  have hv := hB T H U σ hT hU hUT hlog hH hσ a b
  calc
    _ ≤ W*G*(C/(T : ℝ))*(q*R : ℕ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv (mul_nonneg hW0 hG0)) (Nat.cast_nonneg _)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FiniteSmoothedMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from small short-average energy to a finite coefficient sum -/
namespace JointDickman
open Finset

theorem finite_approximation_square_mean {ι κ : Type*} (I : Finset ι) (S : Finset κ)
    (f : ι → ℂ) (a b : ι → κ → ℂ) {X E C ε : ℝ}
    (hX : 0 < X) (hI : (I.card : ℝ) ≤ 2*X)
    (hf : ∀ u ∈ I, ‖f u-∑ j ∈ S, a u j*b u j‖ ≤ E)
    (ha : ∀ u ∈ I, ∀ j ∈ S, ‖a u j‖ ≤ C)
    (hb : ∀ j ∈ S, (1/X)*(∑ u ∈ I, ‖b u j‖^2) ≤ ε) :
    (1/X)*(∑ u ∈ I, ‖f u‖^2) ≤ 4*E^2+2*(S.card : ℝ)^2*C^2*ε := by
  have hpoint (u) (hu : u ∈ I) : ‖f u‖^2 ≤ 2*E^2+2*‖∑ j ∈ S, a u j*b u j‖^2 := by
    have ht := norm_square_le_twice_difference (f u) (∑ j ∈ S, a u j*b u j)
    have hp : ‖f u-∑ j ∈ S, a u j*b u j‖^2 ≤ E^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hf u hu) 2
    have hp2 := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num)
    exact ht.trans (add_le_add hp2 le_rfl)
  have hmean := finite_weighted_square_mean I S a b hX ha hb
  calc
    _ ≤ (1/X)*(∑ u ∈ I, (2*E^2+2*‖∑ j ∈ S, a u j*b u j‖^2)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hpoint) (by positivity)
    _ = (2*(I.card : ℝ)/X)*E^2+2*((1/X)*(∑ u ∈ I, ‖∑ j ∈ S, a u j*b u j‖^2)) := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum]
      ring
    _ ≤ 4*E^2+2*((S.card : ℝ)^2*C^2*ε) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg E)
        apply (div_le_iff₀ hX).mpr
        linarith
      · exact mul_le_mul_of_nonneg_left hmean (by norm_num)
    _ = _ := by ring

theorem succ_card_scaled_square {T : ℕ} (hT : 0 < T) (C : ℝ) :
    ((T : ℝ)+1)^2*(C/(T : ℝ))^2 ≤ 4*C^2 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hr : ((T : ℝ)+1)/(T : ℝ) ≤ 2 := (div_le_iff₀ hT0).mpr (by linarith)
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hr 2) (sq_nonneg C)
  first | (convert hp using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hp.trans (le_of_eq (by ring)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockCutNorm
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite cut norm controls every choice of bounded block labels -/

namespace JointDickman
open Finset

theorem complexEnergy_cutMaximum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    ‖complexEnergy K z‖ ≤ 16*kernelCutMaximum K := by
  classical
  apply complexEnergy_le_sixteen K (kernelCutMaximum K) _ z hz
  intro f g hf hg
  apply realBilinear_bound_of_signs K (kernelCutMaximum K) _ f g hf hg
  intro s t
  exact le_sup' (fun st : (ι → Bool) × (ι → Bool) =>
    |realBilinear K (fun i => cutSign (st.1 i)) (fun j => cutSign (st.2 j))|)
    (mem_univ (s,t))

theorem complexEnergy_re_cutNorm_le (M : ℕ) (K : Fin M → Fin M → ℝ)
    (z : Fin M → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    |(complexEnergy K z).re|/(M : ℝ) ≤ 16*kernelCutNorm K := by
  have h := (Complex.abs_re_le_norm (complexEnergy K z)).trans
    (complexEnergy_cutMaximum_le K z hz)
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  simpa only [kernelCutNorm,Fintype.card_fin,mul_div_assoc] using hd

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMultiplicativeReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := ite_eq_right hn.ne'

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoarseCountingRowsDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem coarse_counting_row_energy_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (D : ℕ) (b₀ : Fin m) {η : ℝ} (hη : 0 < η)
    {q : ℕ} [NeZero q] (F : ZMod q → ℝ) (W : ℝ) (hF : ∀ r, |F r| ≤ W)
    (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (a b : Fin m) (σ : ℕ → ℝ) (U : ℕ → ℕ), (∀ u, |σ u| ≤ 3) →
      (∀ u, 0 < U u ∧ U u ≤ T B) → ∀ v : ℕ, v ≤ M B →
      let g := fun k =>
        (binLabel (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ k-μ)*
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b₀) k : ℂ)
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖∑ j ∈ range (T B+1),
          ((cutLagWeight (H B) (U u) (fun k =>
            countingTermCoefficient P d m B k c D (T B) (σ u) a b/(k : ℝ)) j : ℝ) : ℂ)*
              (F (j : ZMod q) : ℂ)*g (u+v+j)‖^2) < ε := by
  obtain ⟨C,hC,hsmooth⟩ := counting_lag_upper_smoothing hM hMP P d hm c hc D hη
  obtain ⟨V,hV,hweight⟩ := counting_lag_upper_weight_bound hM hMP P d hm c hc D hη
  let G : ℝ := 2/channelMesh m
  have hG : 0 < G := div_pos (by norm_num) (channelMesh_pos hm)
  have hW : 0 ≤ W := (abs_nonneg (F 0)).trans (hF 0)
  let err := fun B => (W*G*C*(q : ℝ))*((R B : ℝ)/(T B : ℝ))
  have herr : Tendsto err atTop (𝓝 0) := by simpa only [mul_zero] using hRT.const_mul (W*G*C*(q : ℝ))
  have herrsq : Tendsto (fun B => 4*(err B)^2) atTop (𝓝 0) := by
    simpa using (herr.pow 2).const_mul 4
  intro ε hε
  let ν := ε/(16*(V*W)^2+1)
  have hν : 0 < ν := by dsimp [ν] <;> positivity
  have hνsmall : 8*(V*W)^2*ν < ε/2 := by
    dsimp [ν]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 16*(V*W)^2+1)).mpr
    nlinarith
  have hshort := coarse_residue_smoothing_energy_proved_jd hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b₀ (q := q) A scale R (fun B => M B+T B) hA hscale hR ν hν
  filter_upwards [hsmooth,hweight,hshort,hvalid,hR.eventually_gt_atTop 0,
    herrsq.eventually (eventually_lt_nhds (half_pos hε))]
    with B hsm hwt hshort hvalidB hRB herrB
  filter_upwards [hshort,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro a b σ U hσ hU v hv g
  let X := A B*scale n
  let I := Ico ⌈X⌉₊ ⌊2*X⌋₊
  let S := range (T B+1)
  let K := fun u => cutLagWeight (H B) (U u) (fun k =>
    countingTermCoefficient P d m B k c D (T B) (σ u) a b/(k : ℝ))
  let α := fun u j => (K u j : ℂ)*(F (j : ZMod q) : ℂ)
  let β := fun u j => residueSmoothed g q (R B) (u+v+j)
  let f := fun u => ∑ j ∈ S, α u j*g (u+v+j)
  have hg : ∀ k, ‖g k‖ ≤ G := fun k => norm_centered_coarse_weight_le _ ζ hζ μ hμ hm B b₀ k
  have happrox (u : ℕ) (_ : u ∈ I) : ‖f u-∑ j ∈ S, α u j*β u j‖ ≤ err B := by
    have hh := hsm (T B) (H B) (U u) (σ u) hvalidB.1 (hU u).1 (hU u).2 hvalidB.2.1 hvalidB.2.2 (hσ u) a b q (R B) (u+v) F g G W hRB hg hF
    change ‖f u-∑ j ∈ S, α u j*β u j‖ ≤ _ at hh
    exact hh.trans_eq (by dsimp [err]; push_cast <;> ring)
  have hα (u : ℕ) (_ : u ∈ I) (j : ℕ) (_ : j ∈ S) : ‖α u j‖ ≤ V*W/(T B : ℝ) := by
    dsimp only [α]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs]
    have hh := mul_le_mul (hwt (T B) (H B) (U u) (σ u) hvalidB.1 hvalidB.2.1 hvalidB.2.2 (hσ u) a b j)
      (hF (j : ZMod q)) (abs_nonneg _) (by positivity : 0 ≤ V/(T B : ℝ))
    exact hh.trans_eq (by ring)
  have hβ (j : ℕ) (hj : j ∈ S) : (1/X)*(∑ u ∈ I, ‖β u j‖^2) ≤ ν := by
    simpa only [β,I,X,Nat.add_assoc] using
      (hn (v+j) (by have hh := mem_range.mp hj; omega)).le
  have hcard : (I.card : ℝ) ≤ 2*X := by
    dsimp only [I]
    rw [Nat.card_Ico]
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (by positivity))
  have hh := finite_approximation_square_mean I S f α β hX hcard happrox hα hβ
  change (1/X)*(∑ u ∈ I, ‖f u‖^2) < ε
  apply hh.trans_lt
  have hfac : (S.card : ℝ)^2*(V*W/(T B : ℝ))^2 ≤ 4*(V*W)^2 := by
    simpa only [S,card_range,Nat.cast_add,Nat.cast_one] using succ_card_scaled_square hvalidB.1 (V*W)
  have hmul := mul_le_mul_of_nonneg_right hfac hν.le
  have hbound : 4*(err B)^2+2*(S.card : ℝ)^2*(V*W/(T B : ℝ))^2*ν ≤
      4*(err B)^2+8*(V*W)^2*ν := by nlinarith
  exact hbound.trans_lt (by linarith)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_DistanceLagSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing a nonnegative error over lags in a finite block -/
namespace JointDickman
open Finset Classical

private theorem forward_lag_sum {M : ℕ} (i : Fin M) (T : ℕ) (E : ℕ → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ k : Fin M, if i < k ∧ k.val-i.val < T then E (k.val-i.val) else 0) ≤
      ∑ j ∈ Ioc 0 T, E j := by
  let I : Finset (Fin M) := univ.filter (fun k => i < k ∧ k.val-i.val < T)
  have hinj : Set.InjOn (fun k : Fin M => k.val-i.val) I := by
    intro k hk l hl he
    have hk' : i.val < k.val := (mem_filter.mp hk).2.1
    have hl' : i.val < l.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    dsimp only at he
    omega
  have hsub : I.image (fun k => k.val-i.val) ⊆ Ioc 0 T := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk := (mem_filter.mp hk).2
    have hik : i.val < k.val := hk.1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ I, E (k.val-i.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => k.val-i.val), E j := (sum_image (f := E) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hE j)

private theorem backward_lag_sum {M : ℕ} (i : Fin M) (T : ℕ) (E : ℕ → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ k : Fin M, if k < i ∧ i.val-k.val < T then E (i.val-k.val) else 0) ≤
      ∑ j ∈ Ioc 0 T, E j := by
  let I : Finset (Fin M) := univ.filter (fun k => k < i ∧ i.val-k.val < T)
  have hinj : Set.InjOn (fun k : Fin M => i.val-k.val) I := by
    intro k hk l hl he
    have hk' : k.val < i.val := (mem_filter.mp hk).2.1
    have hl' : l.val < i.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    dsimp only at he
    omega
  have hsub : I.image (fun k => i.val-k.val) ⊆ Ioc 0 T := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk := (mem_filter.mp hk).2
    have hik : k.val < i.val := hk.1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ I, E (i.val-k.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => i.val-k.val), E j := (sum_image (f := E) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hE j)

theorem distance_lag_sum {M : ℕ} (i : Fin M) (T : ℕ) (E : ℕ → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
      E (Nat.dist i.val k.val) else 0) ≤ 2*∑ j ∈ Ioc 0 T, E j := by
  have he (k : Fin M) :
      (if i ≠ k ∧ Nat.dist i.val k.val < T then E (Nat.dist i.val k.val) else 0) =
      (if i < k ∧ k.val-i.val < T then E (k.val-i.val) else 0) +
      (if k < i ∧ i.val-k.val < T then E (i.val-k.val) else 0) := by
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le,Nat.dist_eq_sub_of_le h.le]
    · simp
    · simp [h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le,Nat.dist_eq_sub_of_le_right h.le]
  simp_rw [he]
  rw [sum_add_distrib]
  linarith [forward_lag_sum i T E hE,backward_lag_sum i T E hE]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingPeriodicModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the singular series in the actual finite-feature graph -/
namespace JointDickman
open Finset Classical

theorem countingSiteWithSeries_original
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ) :
    countingSiteWithSeries singularSeries P m B L T H M τ C c D σ =
      countingSiteModel P m B L T H M τ C c D σ := rfl

theorem countingCandidateWithSeries_difference
    (F G : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {T σ K : ℝ}
    (hK : ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K)
    (S R : Finset ℕ) :
    |countingCandidateWithSeries F P m B L j τ C c D T σ S R-
      countingCandidateWithSeries G P m B L j τ C c D T σ S R| ≤
      (independentRootMean B L τ C/(j : ℝ))*|F j-G j| *K := by
  have hr := independentRootMean_nonneg B L τ C
  have he : countingCandidateWithSeries F P m B L j τ C c D T σ S R-
      countingCandidateWithSeries G P m B L j τ C c D T σ S R =
      (independentRootMean B L τ C/(j : ℝ))*(F j-G j)*
        subsetPrimeModel B (fun x y => countingPrimeKernel P m B j c D T σ y x) S R := by
    unfold countingCandidateWithSeries
    ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg (div_nonneg hr (Nat.cast_nonneg j))]
  exact mul_le_mul_of_nonneg_left (hK _ _) (mul_nonneg (by positivity) (abs_nonneg _))

theorem countingSiteWithSeries_difference
    (F G : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {σ η K : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hK : 0 ≤ K) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteWithSeries F P m B L T H M τ C c D σ i k a b-
      countingSiteWithSeries G P m B L T H M τ C c D σ i k a b| ≤
      if i ≠ k ∧ Nat.dist i.val k.val < T then
        (independentRootMean B L τ C*K/(η*T))*|F (Nat.dist i.val k.val)-G (Nat.dist i.val k.val)|
      else 0 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hr := independentRootMean_nonneg B L τ C
  have hc (j : ℕ) (hj : H < j) (hjt : j < T) (a b : Finset ℕ) :
      |countingCandidateWithSeries F P m B L j τ C c D T σ a b-
        countingCandidateWithSeries G P m B L j τ C c D T σ a b| ≤
        (independentRootMean B L τ C*K/(η*T))*|F j-G j| := by
    have hjr : η*(T : ℝ) ≤ j := hH.trans (by exact_mod_cast hj.le)
    have hj0 : (0 : ℝ) < j := (mul_pos hη hTr).trans_le hjr
    have hdiv := one_div_le_one_div_of_le (mul_pos hη hTr) hjr
    have hmul := mul_le_mul_of_nonneg_left hdiv (mul_nonneg (mul_nonneg hr hK) (abs_nonneg (F j-G j)))
    calc
      _ ≤ (independentRootMean B L τ C/(j : ℝ))*|F j-G j| *K :=
        countingCandidateWithSeries_difference F G P m B L j τ C c D (hbound j hj hjt) a b
      _ ≤ _ := by convert hmul using 1 <;> first | (with_reducible_and_instances rfl) | ring
  unfold countingSiteWithSeries
  rcases lt_trichotomy i k with hik | rfl | hki
  · rw [ite_eq_left hik,ite_eq_left hik,Nat.dist_eq_sub_of_le hik.le]
    by_cases h : H < k.val-i.val ∧ k.val-i.val < T
    · rw [ite_eq_left h,ite_eq_left h,ite_eq_left ⟨ne_of_lt hik,h.2⟩]
      exact hc _ h.1 h.2 _ _
    · rw [ite_eq_right h,ite_eq_right h,sub_self,abs_zero]
      split_ifs <;> positivity
  · simp
  · rw [ite_eq_right (not_lt_of_ge hki.le),ite_eq_right (not_lt_of_ge hki.le),ite_eq_left hki,ite_eq_left hki,
      Nat.dist_eq_sub_of_le_right hki.le]
    by_cases h : H < i.val-k.val ∧ i.val-k.val < T
    · rw [ite_eq_left h,ite_eq_left h,ite_eq_left ⟨Ne.symm (ne_of_lt hki),h.2⟩]
      exact hc _ h.1 h.2 _ _
    · rw [ite_eq_right h,ite_eq_right h,sub_self,abs_zero]
      split_ifs <;> positivity

theorem countingSiteWithSeries_cut_error
    (F G : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {σ η K R δ : ℝ}
    (hT : 0 < T) (hM : 0 < M) (hη : 0 < η) (hK : 0 ≤ K)
    (hroot : independentRootMean B L τ C ≤ R) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K)
    (hmean : ∑ j ∈ Ioc 0 T, |F j-G j| ≤ δ*T)
    (x : Fin M → (auxiliaryPrimes B).powerset) :
    kernelCutNorm (realizedSiteKernel
      (fun i k a b => countingSiteWithSeries F P m B L T H M τ C c D σ i k a b-
        countingSiteWithSeries G P m B L T H M τ C c D σ i k a b) x) ≤ 2*R*K*δ/η := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hr := independentRootMean_nonneg B L τ C
  have hrow (i : Fin M) :
      (∑ k, |countingSiteWithSeries F P m B L T H M τ C c D σ i k (x i) (x k)-
        countingSiteWithSeries G P m B L T H M τ C c D σ i k (x i) (x k)|) ≤
        2*R*K*δ/η := by
    calc
      _ ≤ ∑ k, if i ≠ k ∧ Nat.dist i.val k.val < T then
          (independentRootMean B L τ C*K/(η*T))*|F (Nat.dist i.val k.val)-G (Nat.dist i.val k.val)| else 0 :=
        sum_le_sum (fun k _ => countingSiteWithSeries_difference F G P m B L T H M τ C c D
          hT hη hK hH hbound i k (x i) (x k))
      _ = (independentRootMean B L τ C*K/(η*T))*
          (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
            |F (Nat.dist i.val k.val)-G (Nat.dist i.val k.val)| else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        split_ifs <;> simp
      _ ≤ (independentRootMean B L τ C*K/(η*T))*(2*(δ*T)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (distance_lag_sum i T (fun j => |F j-G j|) (fun _ => abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hmean (by norm_num))
      _ ≤ (R*K/(η*T))*(2*(δ*T)) := by
        have hδT : 0 ≤ δ*(T : ℝ) := (sum_nonneg (fun j _ => abs_nonneg (F j-G j))).trans hmean
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hK) (by positivity)
      _ = _ := by field_simp
  apply (kernelCutNorm_le_absolute_mass _).trans
  unfold kernelAbsoluteMass realizedSiteKernel
  simp only [Fintype.card_fin]
  apply (div_le_iff₀ hMr).mpr
  calc
    _ ≤ ∑ _i : Fin M, 2*R*K*δ/η := sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp <;> ring

/-- A fixed finite residue function suffices uniformly for all block sizes. -/
theorem countingSiteModel_periodic_approximation
    (hMP : PublishedInputs.PrimeProductMertensInput) {R K η ε : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hη : 0 < η) (hε : 0 < ε) :
    ∃ (q : ℕ) (_ : NeZero q) (F : ZMod q → ℝ),
      ∀ (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
        (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
        (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ),
        0 < T → 0 < M → independentRootMean B L τ C ≤ R → η*T ≤ H →
        (∀ j : ℕ, H < j → j < T →
          ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K) →
        ∀ x : Fin M → (auxiliaryPrimes B).powerset,
        kernelCutNorm (realizedSiteKernel
          (fun i k a b => countingSiteModel P m B L T H M τ C c D σ i k a b-
            countingSiteWithSeries (fun j => F (j : ZMod q)) P m B L T H M τ C c D σ i k a b) x) ≤ ε := by
  let δ := ε*η/(2*(R+1)*(K+1))
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  obtain ⟨q,hq,F,hF⟩ := singularSeries_periodic_approximation hMP hδ
  refine ⟨q,hq,F,?_⟩
  intro P m B L T H M τ C c D σ hT hM hroot hH hbound x
  rw [← countingSiteWithSeries_original]
  apply (countingSiteWithSeries_cut_error singularSeries (fun j => F (j : ZMod q))
    P m B L T H M τ C c D hT hM hη hK hroot hH hbound (hF T) x).trans
  have hprod : R*K ≤ (R+1)*(K+1) := by nlinarith
  calc
    2*R*K*δ/η = ε*(R*K/((R+1)*(K+1))) := by dsimp [δ]; field_simp
    _ ≤ ε*1 := mul_le_mul_of_nonneg_left
      ((div_le_one (by positivity : 0 < (R+1)*(K+1))).mpr hprod) hε.le
    _ = ε := mul_one _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingArithmeticCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact arithmetic evaluation of the periodic finite-feature coefficient -/
namespace JointDickman
open Finset Classical

theorem coefficientPrimeSet_feature_input (B n : ℕ) :
    (fun p : auxiliaryPrimes B => decide (p.val ∈ coefficientPrimeSet B n)) =
      (fun p : auxiliaryPrimes B => decide (p.val ∣ n)) := by
  funext p
  simp only [coefficientPrimeSet,mem_filter,p.property,true_and]

theorem countingCandidateWithSeries_arithmetic (F : ℕ → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) {n v : ℕ} (hn : n ≠ 0) (hv : v ≠ 0) :
    countingCandidateWithSeries F P m B L j τ C c D T σ
      (coefficientPrimeSet B n) (coefficientPrimeSet B v) =
    (independentRootMean B L τ C*(F j/(j : ℝ)))*
      ∑ d ∈ P.support, ∑ a, ∑ b, countingTermCoefficient P d (m d) B j (c d) (D d) T σ a b*
        primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B a) v*
        primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B b) n := by
  unfold countingCandidateWithSeries subsetPrimeModel
  rw [coefficientPrimeSet_feature_input,coefficientPrimeSet_feature_input]
  dsimp only
  rw [countingPrimeKernel_coefficients]
  simp only [primeSiteWeight_apply _ _ hn,primeSiteWeight_apply _ _ hv]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FiniteForwardLagSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact forward-row parametrization by the positive lag -/
namespace JointDickman
open Finset Classical

theorem sum_fin_forward_lags {M : ℕ} (i : Fin M) (H T : ℕ) (f : ℕ → ℂ) :
    (∑ k : Fin M, if i < k ∧ H < k.val-i.val ∧ k.val-i.val < T then f (k.val-i.val) else 0) =
      ∑ j ∈ range (T+1), if H < j ∧ j < min T (M-i.val) then f j else 0 := by
  rw [← sum_filter,← sum_filter]
  apply sum_bij (fun k _ => k.val-i.val)
  · intro k hk
    have hh := (mem_filter.mp hk).2
    have hik : i.val < k.val := hh.1
    simp only [mem_filter,mem_range,lt_min_iff]
    exact ⟨by omega,hh.2.1,hh.2.2,by omega⟩
  · intro k hk l hl hkl
    have hk' : i.val < k.val := (mem_filter.mp hk).2.1
    have hl' : i.val < l.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    omega
  · intro j hj
    have hh := mem_filter.mp hj
    have hb := lt_min_iff.mp hh.2.2
    have hij : i.val+j < M := by omega
    refine ⟨⟨i.val+j,hij⟩,?_,?_⟩
    · simp only [mem_filter,mem_univ,true_and,Fin.lt_def]
      exact ⟨by omega,by simpa using hh.2.1,by simpa using hb.1⟩
    · simp
  · intro k _
    rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingForwardRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The periodic graph row as a finite-feature convolution -/
namespace JointDickman
open Finset Classical

theorem countingForwardRow_lag (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) :
    countingForwardRow F P m B L T H M u τ C c D σ z i =
      ∑ j ∈ range (T+1), if H < j ∧ j < min T (M-i.val) then
        (countingCandidateWithSeries F P m B L j τ C c D T σ
          (coefficientPrimeSet B (u+(i.val+1)))
          (coefficientPrimeSet B (u+(i.val+1)+j)) : ℂ)*
          star (z (u+(i.val+1)))*z (u+(i.val+1)+j) else 0 := by
  rw [← sum_fin_forward_lags i H T]
  unfold countingForwardRow
  apply sum_congr rfl
  intro k _
  by_cases hik : i < k
  · have hn : u+(i.val+1)+(k.val-i.val) = u+(k.val+1) := by
      have hh : i.val < k.val := hik
      omega
    simp only [ite_eq_left hik,countingSiteWithSeries,hn]
    by_cases hj : H < k.val-i.val ∧ k.val-i.val < T
    · simp [hik,hj.1,hj.2]
    · simp [hj]
  · simp [hik]

theorem countingForwardRow_features (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) :
    countingForwardRow F P m B L T H M u τ C c D σ z i =
      (independentRootMean B L τ C : ℂ)*
        ∑ d ∈ P.support, ∑ a, ∑ b,
          ((primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B b)
            (u+(i.val+1)) : ℝ) : ℂ)*star (z (u+(i.val+1)))*
            countingTermRow F P d (m d) B T H M u (c d) (D d) σ z i a b := by
  rw [countingForwardRow_lag]
  have hpoint (j : ℕ) :
      (if H < j ∧ j < min T (M-i.val) then
        (countingCandidateWithSeries F P m B L j τ C c D T σ
          (coefficientPrimeSet B (u+(i.val+1)))
          (coefficientPrimeSet B (u+(i.val+1)+j)) : ℂ)*
          star (z (u+(i.val+1)))*z (u+(i.val+1)+j) else 0) =
      (independentRootMean B L τ C : ℂ)*
        ∑ d ∈ P.support, ∑ a, ∑ b,
          ((primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B b)
            (u+(i.val+1)) : ℝ) : ℂ)*star (z (u+(i.val+1)))*
          (((cutLagWeight H (min T (M-i.val)) (fun k =>
            countingTermCoefficient P d (m d) B k (c d) (D d) T σ a b/(k : ℝ)) j : ℝ) : ℂ)*
            (F j : ℂ)*(z (u+(i.val+1)+j)*
              (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B a)
                (u+(i.val+1)+j) : ℂ))) := by
    by_cases hj : H < j ∧ j < min T (M-i.val)
    · rw [ite_eq_left hj,countingCandidateWithSeries_arithmetic F P m B L j τ C c D T σ
        (by omega) (by omega)]
      simp only [cutLagWeight,ite_eq_left hj]
      push_cast
      simp only [mul_sum,sum_mul]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
    · simp only [cutLagWeight,ite_eq_right hj,Complex.ofReal_zero,zero_mul,mul_zero,sum_const_zero]
  simp_rw [hpoint]
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [← mul_sum]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingFeatureRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single finite index for the actual counting-model row -/
namespace JointDickman
open Finset Classical

theorem countingForwardRow_features_flat (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) :
    countingForwardRow F P m B L T H M u τ C c D σ z i =
      ∑ e : CountingFeatureIndex P m,
        ((independentRootMean B L τ C : ℂ)*
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m e.1.val) B e.2.2)
            (u+(i.val+1)) : ℂ)*star (z (u+(i.val+1))))*
          countingTermRow F P e.1.val (m e.1.val) B T H M u
            (c e.1.val) (D e.1.val) σ z i e.2.1 e.2.2 := by
  rw [countingForwardRow_features]
  simp only [CountingFeatureIndex,Fintype.sum_sigma,Fintype.sum_prod_type]
  rw [sum_coe_sort P.support (fun d => ∑ a : Fin (m d), ∑ b : Fin (m d),
    ((independentRootMean B L τ C : ℂ)*
      (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B b)
        (u+(i.val+1)) : ℂ)*star (z (u+(i.val+1))))*
      countingTermRow F P d (m d) B T H M u (c d) (D d) σ z i a b)]
  simp only [mul_sum]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingForwardEnergyDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem counting_forward_row_energy_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2)) (D : (Fin 4 →₀ ℕ) → ℕ)
    {η : ℝ} (hη : 0 < η) {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (W : ℝ) (hF : ∀ r, |F r| ≤ W)
    (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
    (hA : ∀ B, 0 < A B) (hscale : Tendsto scale atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
    {V : ℝ} (hV : 0 ≤ V) (hroot : ∀ᶠ B in atTop, independentRootMean B L τ C ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) → ∀ i : Fin (M B),
      let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖countingForwardRow (fun j => F (j : ZMod q)) P m B L (T B) (H B) (M B) u
          τ C c D (σ u) z i‖^2) < ε := by
  let I := CountingFeatureIndex P m
  let K : ℝ := ∑ e : I, V*(2/channelMesh (m e.1.val))
  have hK : 0 ≤ K := sum_nonneg (fun e _ => mul_nonneg hV (by
    exact div_nonneg (by norm_num) (channelMesh_pos (hm e.1.val)).le))
  intro ε hε
  let ν := ε/((Fintype.card I : ℝ)^2*K^2+1)
  have hν : 0 < ν := by dsimp [ν] <;> positivity
  have hsmall : (Fintype.card I : ℝ)^2*K^2*ν < ε := by
    dsimp [ν]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < (Fintype.card I : ℝ)^2*K^2+1)).mpr
    nlinarith
  have hshort (e : I) := coarse_counting_row_energy_proved hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean P e.1.val (hm e.1.val) (c e.1.val) (hc e.1.val)
    (D e.1.val) e.2.1 hη (q := q) F W hF A scale T H R M hA hscale hR hRT hvalid ν hν
  filter_upwards [eventually_all.mpr hshort,hroot,hvalid] with B hshort hrootB hvalidB
  filter_upwards [eventually_all.mpr hshort,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0]
    with n hn hX
  intro σ hσ i z
  let X := A B*scale n
  let S := Ico ⌈X⌉₊ ⌊2*X⌋₊
  let α := fun u (e : I) => (independentRootMean B L τ C : ℂ)*
    (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m e.1.val) B e.2.2)
      (u+(i.val+1)) : ℂ)*star (z (u+(i.val+1)))
  let β := fun u (e : I) => countingTermRow (fun j => F (j : ZMod q)) P e.1.val
    (m e.1.val) B (T B) (H B) (M B) u (c e.1.val) (D e.1.val) (σ u) z i e.2.1 e.2.2
  have hα (u : ℕ) (_ : u ∈ S) (e : I) (_ : e ∈ univ) : ‖α u e‖ ≤ K := by
    have hb := norm_centered_coarse_weight_le
      (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ hζ μ hμ
      (hm e.1.val) B e.2.2 (u+(i.val+1))
    change ‖z (u+(i.val+1))*
      (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m e.1.val) B e.2.2)
        (u+(i.val+1)) : ℂ)‖ ≤ _ at hb
    rw [norm_mul] at hb
    have hn : ‖α u e‖ ≤ V*(2/channelMesh (m e.1.val)) := by
      dsimp only [α]
      rw [mul_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (independentRootMean_nonneg B L τ C),norm_mul,norm_star,mul_comm _ ‖z _‖]
      exact mul_le_mul hrootB hb (by positivity) hV
    exact hn.trans (single_le_sum (fun f _ => mul_nonneg hV
      (div_nonneg (by norm_num) (channelMesh_pos (hm f.1.val)).le)) (mem_univ e))
  have hβ (e : I) (_ : e ∈ univ) : (1/X)*(∑ u ∈ S, ‖β u e‖^2) ≤ ν := by
    have hU : 0 < min (T B) (M B-i.val) ∧ min (T B) (M B-i.val) ≤ T B :=
      ⟨lt_min hvalidB.1 (by omega),min_le_left _ _⟩
    simpa only [X,S,β,countingTermRow,Nat.add_assoc] using
      (hn e e.2.1 e.2.2 σ (fun _ => min (T B) (M B-i.val)) hσ (fun _ => hU)
        (i.val+1) (by omega)).le
  have hh := finite_weighted_square_mean S (univ : Finset I) α β hX hα hβ
  simp only [card_univ] at hh
  have heq (u : ℕ) : countingForwardRow (fun j => F (j : ZMod q)) P m B L
      (T B) (H B) (M B) u τ C c D (σ u) z i = ∑ e : I, α u e*β u e :=
    countingForwardRow_features_flat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp_rw [heq]
  exact hh.trans_lt hsmall

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingKernelBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for the actual counting prime kernel -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem countingPrimeKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (D : (Fin 4 →₀ ℕ) → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T σ : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → |σ| ≤ 3 →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K := by
  obtain ⟨K,hK,hbound⟩ := weightedPolynomialPrimeKernel_bounded hM hMP P m hm c hc D
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 30] with B hb hB
  intro j T σ hT hlog hσ x y
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  have hS : ∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*Real.log 2)/T) := by
    intro k hk
    exact (((dyadic_scale_window hB hT hlog).2.1 k hk).2).1
  let r := fun k : ℤ => amplificationBump (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)
  have hr : ∀ k ∈ S, |r k| ≤ 1 := by
    intro k _
    rw [abs_of_nonneg (amplificationBump_bounds _).1]
    exact (amplificationBump_bounds _).2
  exact hb j T S hS (fun _ => σ) (fun _ _ => hσ) r hr x y

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ForwardQuadraticEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering a symmetric quadratic form from its forward rows -/
namespace JointDickman
open Finset Classical

theorem complexEnergy_eq_forward_add_star {M : ℕ} (K : Fin M → Fin M → ℝ)
    (hK : ∀ i k, K i k = K k i) (hdiag : ∀ i, K i i = 0) (z : Fin M → ℂ) :
    complexEnergy K z = (∑ i, forwardKernelRow K z i)+star (∑ i, forwardKernelRow K z i) := by
  have hback : star (∑ i, forwardKernelRow K z i) =
      ∑ i, ∑ k, if k < i then (K i k : ℂ)*star (z i)*z k else 0 := by
    simp only [forwardKernelRow,star_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k _
    by_cases h : k < i
    · simp only [ite_eq_left h,star_mul,Complex.star_def,Complex.conj_ofReal,starRingEnd_self_apply]
      rw [hK k i]
      ring
    · simp only [ite_eq_right h,star_zero]
  rw [hback]
  simp only [complexEnergy,forwardKernelRow,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro k _
  rcases lt_trichotomy i k with h | rfl | h
  · simp [h,not_lt_of_ge h.le]
  · simp [hdiag]
  · simp [h,not_lt_of_ge h.le]

theorem normalized_complexEnergy_sq_le_forward {M : ℕ} (hM : 0 < M)
    (K : Fin M → Fin M → ℝ) (hK : ∀ i k, K i k = K k i)
    (hdiag : ∀ i, K i i = 0) (z : Fin M → ℂ) :
    (‖complexEnergy K z‖/(M : ℝ))^2 ≤
      (4/(M : ℝ))*(∑ i, ‖forwardKernelRow K z i‖^2) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hn : ‖complexEnergy K z‖ ≤ 2*‖∑ i, forwardKernelRow K z i‖ := by
    rw [complexEnergy_eq_forward_add_star K hK hdiag]
    exact (norm_add_le _ _).trans_eq (by rw [norm_star]; ring)
  have hs := finite_weighted_square_bound (univ : Finset (Fin M))
    (fun _ => (1 : ℂ)) (forwardKernelRow K z) (C := 1) (by simp)
  simp only [one_mul,card_univ,Fintype.card_fin,one_pow,mul_one] at hs
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hMr)).mpr
  field_simp
  nlinarith

theorem symmetric_energy_square_mean {M : ℕ} (hM : 0 < M) (S : Finset ℕ)
    (K : ℕ → Fin M → Fin M → ℝ) (z : ℕ → Fin M → ℂ)
    (hK : ∀ u i k, K u i k = K u k i) (hdiag : ∀ u i, K u i i = 0)
    {X δ : ℝ} (hX : 0 < X)
    (hrow : ∀ i, (1/X)*(∑ u ∈ S, ‖forwardKernelRow (K u) (z u) i‖^2) ≤ δ) :
    (1/X)*(∑ u ∈ S, (‖complexEnergy (K u) (z u)‖/(M : ℝ))^2) ≤ 4*δ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ (1/X)*(∑ u ∈ S, (4/(M : ℝ))*∑ i, ‖forwardKernelRow (K u) (z u) i‖^2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun u _ =>
        normalized_complexEnergy_sq_le_forward hM (K u) (hK u) (hdiag u) (z u))) (by positivity)
    _ = (4/(M : ℝ))*∑ i, (1/X)*(∑ u ∈ S, ‖forwardKernelRow (K u) (z u) i‖^2) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro u _
      ring
    _ ≤ (4/(M : ℝ))*∑ _i : Fin M, δ :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hrow i)) (by positivity)
    _ = _ := by simp; field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingPeriodicEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the actual periodic finite graph -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem countingArithmeticKernel_diag (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ) (i : Fin M) :
    countingArithmeticKernel F P m B L T H M u τ C c D σ i i = 0 := by
  simp only [countingArithmeticKernel,countingSiteWithSeries,lt_self_iff_false,ite_false, if_false]

theorem countingArithmeticKernel_symm (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ) (i k : Fin M) :
    countingArithmeticKernel F P m B L T H M u τ C c D σ i k =
      countingArithmeticKernel F P m B L T H M u τ C c D σ k i := by
  rcases lt_trichotomy i k with h | rfl | h
  · simp only [countingArithmeticKernel,countingSiteWithSeries,h,not_lt_of_ge h.le,ite_true, if_true,ite_false, if_false]
  · rfl
  · simp only [countingArithmeticKernel,countingSiteWithSeries,h,not_lt_of_ge h.le,ite_true, if_true,ite_false, if_false]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EnergyMeanComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from periodic mean-square energy to mean energy -/
namespace JointDickman
open Finset Classical

theorem complexEnergy_sub {ι : Type*} [Fintype ι]
    (K J : ι → ι → ℝ) (z : ι → ℂ) :
    complexEnergy (fun i k => K i k-J i k) z = complexEnergy K z-complexEnergy J z := by
  simp only [complexEnergy,Complex.ofReal_sub,sub_mul,sum_sub_distrib]

theorem normalized_energy_comparison {M : ℕ} (hM : 0 < M)
    (K J : Fin M → Fin M → ℝ) (z : Fin M → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    |(complexEnergy K z).re|/(M : ℝ) ≤ |(complexEnergy J z).re|/(M : ℝ)+
      16*kernelCutNorm (fun i k => K i k-J i k) := by
  have h := complexEnergy_re_cutNorm_le M (fun i k => K i k-J i k) z hz
  rw [complexEnergy_sub,Complex.sub_re] at h
  have ht : |(complexEnergy K z).re| ≤
      |(complexEnergy K z).re-(complexEnergy J z).re|+|(complexEnergy J z).re| := by
    simpa only [sub_add_cancel] using abs_add_le
      ((complexEnergy K z).re-(complexEnergy J z).re) (complexEnergy J z).re
  apply (div_le_div_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ M)).trans
  rw [add_div]
  linarith

theorem finite_norm_mean_of_square {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    {X t δ : ℝ} (hX : 0 < X) (ht : 0 < t) (hcard : (S.card : ℝ) ≤ 2*X)
    (hsquare : (1/X)*(∑ i ∈ S, ‖f i‖^2) ≤ δ) :
    (1/X)*(∑ i ∈ S, ‖f i‖) ≤ 2*t+δ/(4*t) := by
  have hp (i : ι) : ‖f i‖ ≤ t+‖f i‖^2/(4*t) := by
    have hh : ‖f i‖*(4*t) ≤ t*(4*t)+‖f i‖^2 := by
      nlinarith [sq_nonneg (‖f i‖-2*t)]
    have hd := (le_div_iff₀ (by positivity : 0 < 4*t)).mpr hh
    exact hd.trans_eq (by field_simp)
  calc
    _ ≤ (1/X)*(∑ i ∈ S, (t+‖f i‖^2/(4*t))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hp i)) (by positivity)
    _ = ((S.card : ℝ)/X)*t+((1/X)*(∑ i ∈ S, ‖f i‖^2))/(4*t) := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul,← sum_div]
      ring
    _ ≤ 2*t+δ/(4*t) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ ht.le
        exact (div_le_iff₀ hX).mpr hcard
      · exact div_le_div_of_nonneg_right hsquare (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingPeriodicEnergyDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem counting_periodic_energy_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2)) (D : (Fin 4 →₀ ℕ) → ℕ)
    {η : ℝ} (hη : 0 < η) {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (W : ℝ) (hF : ∀ r, |F r| ≤ W)
    (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
    (hA : ∀ B, 0 < A B) (hscale : Tendsto scale atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
    (hMpos : ∀ᶠ B in atTop, 0 < M B)
    {V : ℝ} (hV : 0 ≤ V) (hroot : ∀ᶠ B in atTop, independentRootMean B L τ C ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) →
      let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        (‖complexEnergy (countingArithmeticKernel (fun j => F (j : ZMod q)) P m B L
          (T B) (H B) (M B) u τ C c D (σ u))
          (fun i => z (u+(i.val+1)))‖/(M B : ℝ))^2) < ε := by
  intro ε hε
  have hrows := counting_forward_row_energy_proved hKMT hM hSD hSW hMP hJ ζ hζ μ hμ
    hmean P m hm c hc D hη F W hF A scale T H R M L τ C hA hscale hR hRT hvalid hV hroot
    (ε/8) (by positivity)
  filter_upwards [hrows,hMpos] with B hB hMB
  filter_upwards [hB,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro σ hσ z
  let S := Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊
  apply (symmetric_energy_square_mean hMB S
    (fun u => countingArithmeticKernel (fun j => F (j : ZMod q)) P m B L
      (T B) (H B) (M B) u τ C c D (σ u))
    (fun u i => z (u+(i.val+1)))
    (fun u i k => countingArithmeticKernel_symm ..)
    (fun u i => countingArithmeticKernel_diag ..) hX
    (fun i => (hn σ hσ i).le)).trans_lt
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingModelMeanDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem counting_model_energy_mean_proved_jd_oai
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2)) (D : (Fin 4 →₀ ℕ) → ℕ)
    {η : ℝ} (hη : 0 < η)
    (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
    (hA : ∀ B, 0 < A B) (hscale : Tendsto scale atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
    (hMpos : ∀ᶠ B in atTop, 0 < M B)
    {V : ℝ} (hV : 0 ≤ V) (hroot : ∀ᶠ B in atTop, independentRootMean B L τ C ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) →
      let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        (|(complexEnergy (countingArithmeticKernel singularSeries P m B L
          (T B) (H B) (M B) u τ C c D (σ u))
          (fun i => z (u+(i.val+1)))).re|/(M B : ℝ))) < ε := by
  obtain ⟨K,hK,hbound⟩ := countingPrimeKernel_bounded hM hMP P m hm c hc D
  intro ε hε
  let δ := ε/128
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  obtain ⟨q,hq,F,happrox⟩ := countingSiteModel_periodic_approximation hMP hV hK hη hδ
  let : NeZero q := hq
  let W := ∑ r : ZMod q, |F r|
  have hF (r : ZMod q) : |F r| ≤ W := single_le_sum (fun s _ => abs_nonneg (F s)) (mem_univ r)
  let t := ε/8
  have ht : 0 < t := by dsimp [t] <;> positivity
  have henergy := counting_periodic_energy_proved hKMT hM hSD hSW hMP hJ ζ hζ μ hμ hmean
    P m hm c hc D hη F W hF A scale T H R M L τ C hA hscale hR hRT hvalid hMpos hV hroot
    (t^2) (sq_pos_of_pos ht)
  filter_upwards [henergy,hbound,hvalid,hMpos,hroot] with B henergy hbound hvalidB hMB hrootB
  filter_upwards [henergy,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro σ hσ z
  let X := A B*scale n
  let S := Ico ⌈X⌉₊ ⌊2*X⌋₊
  let K₁ := fun u => countingArithmeticKernel singularSeries P m B L (T B) (H B) (M B) u τ C c D (σ u)
  let K₂ := fun u => countingArithmeticKernel (fun j => F (j : ZMod q)) P m B L (T B) (H B) (M B) u τ C c D (σ u)
  let zs := fun u (i : Fin (M B)) => z (u+(i.val+1))
  let f := fun u => complexEnergy (K₂ u) (zs u)/(M B : ℂ)
  have hcard : (S.card : ℝ) ≤ 2*X := by
    dsimp only [S]
    rw [Nat.card_Ico]
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (by positivity))
  have hf : (1/X)*(∑ u ∈ S, ‖f u‖^2) ≤ t^2 := by
    simpa only [f,K₂,zs,norm_div,Complex.norm_natCast] using (hn σ hσ).le
  have hfmean := finite_norm_mean_of_square S f hX ht hcard hf
  have hcut (u : ℕ) : kernelCutNorm (fun i k => K₁ u i k-K₂ u i k) ≤ δ := by
    have hh := happrox P m B L (T B) (H B) (M B) τ C c D (σ u) hvalidB.1 hMB hrootB
      hvalidB.2.2 (fun j _ _ => hbound j (T B) (σ u) (by exact_mod_cast hvalidB.1)
        hvalidB.2.1 (hσ u))
      (fun i => ⟨coefficientPrimeSet B (u+(i.val+1)),by simp [coefficientPrimeSet]⟩)
    exact hh
  have hpoint (u : ℕ) : |(complexEnergy (K₁ u) (zs u)).re|/(M B : ℝ) ≤ ‖f u‖+16*δ := by
    apply (normalized_energy_comparison hMB (K₁ u) (K₂ u) (zs u)
      (fun i => norm_centered_binLabel_le_two _ ζ hζ μ hμ _)).trans
    apply add_le_add
    · simpa only [f,norm_div,Complex.norm_natCast] using
        div_le_div_of_nonneg_right (Complex.abs_re_le_norm (complexEnergy (K₂ u) (zs u))) (Nat.cast_nonneg (M B))
    · exact mul_le_mul_of_nonneg_left (hcut u) (by norm_num)
  change (1/X)*(∑ u ∈ S, |(complexEnergy (K₁ u) (zs u)).re|/(M B : ℝ)) < ε
  calc
    _ ≤ (1/X)*(∑ u ∈ S, (‖f u‖+16*δ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun u _ => hpoint u)) (by positivity)
    _ = (1/X)*(∑ u ∈ S, ‖f u‖)+(S.card : ℝ)/X*(16*δ) := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul]
      ring
    _ ≤ 2*t+(t^2)/(4*t)+2*(16*δ) := by
      apply add_le_add hfmean
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hX).mpr hcard) (by positivity)
    _ < ε := by
      have hdiv : t^2/(4*t) = t/4 := by field_simp
      rw [hdiv]
      dsimp [t,δ]
      linarith

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.counting_model_energy_mean_proved_jd_oai := @OAI.JointDickman.counting_model_energy_mean_proved_jd_oai
