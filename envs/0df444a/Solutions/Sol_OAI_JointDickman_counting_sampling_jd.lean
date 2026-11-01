-- Prove2me | solution 1 for OAI.JointDickman.counting_sampling_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:10:17.267922+00:00
-- url     : https://prove2.me/submissions/607c112c-211d-4fd2-b425-f5bd3937536d

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_counting_block_test_jd
import Theorems.Thm_OAI_JointDickman_latentPrimeSiteKernel_row_mean_jd
import Theorems.Thm_OAI_JointDickman_latentPrimeSiteKernel_row_square_mass_jd

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- A fixed power times a logarithm is smaller than any strictly larger
power. The base tends through positive reals. -/
theorem power_mul_log_isLittleO {a b : ℝ} (hab : a < b) :
    (fun B : ℝ => B ^ a * Real.log B) =o[atTop] (fun B => B ^ b) := by
  have h := (isLittleO_log_rpow_atTop (sub_pos.mpr hab)).mul_isBigO
    (isBigO_refl (fun B : ℝ => B ^ a) atTop)
  apply h.congr'
  · exact Eventually.of_forall (fun B => mul_comm _ _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    rw [← Real.rpow_add hB]
    congr 1
    ring

theorem power_mul_log_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => (B ^ a * Real.log B) / B ^ b)
      atTop (𝓝 0) :=
  (power_mul_log_isLittleO hab).tendsto_div_nhds_zero

/-- The union-bound entropy is absorbed by the negative concentration
exponent whenever the latter has a strictly larger positive power. -/
theorem exp_power_log_sub_power_tendsto_zero {a b c : ℝ}
    (hab : a < b) (hb : 0 < b) (hc : 0 < c) (C : ℝ) :
    Tendsto (fun B : ℝ => Real.exp (C * (B ^ a * Real.log B) - c * B ^ b))
      atTop (𝓝 0) := by
  have hquot : Tendsto (fun B : ℝ => C * ((B ^ a * Real.log B) / B ^ b) - c)
      atTop (𝓝 (-c)) := by
    simpa using ((power_mul_log_div_power_tendsto_zero hab).const_mul C).sub_const c
  have hexponent := hquot.neg_mul_atTop (by linarith) (tendsto_rpow_atTop hb)
  have heq : (fun B : ℝ => (C * ((B ^ a * Real.log B) / B ^ b) - c) * B ^ b)
      =ᶠ[atTop] (fun B => C * (B ^ a * Real.log B) - c * B ^ b) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    have hpow := (Real.rpow_pos_of_pos hB b).ne'
    field_simp
  exact Real.tendsto_exp_atBot.comp (hexponent.congr' heq)

theorem sampling_union_bound_tendsto_zero {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Tendsto (fun B : ℝ => Real.exp
      (C * (B ^ (14 / 100 : ℝ) * Real.log B) - c * B ^ (18 / 100 : ℝ)))
      atTop (𝓝 0) :=
  exp_power_log_sub_power_tendsto_zero (by norm_num) (by norm_num) hc C

/-- Every smaller real power is negligible compared with a larger one. -/
theorem power_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => B ^ a / B ^ b) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [← Real.rpow_sub hB]
  congr 1
  ring

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
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem bernoulliSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S = 1 := by
  simp only [bernoulliSubsetMass]
  rw [← Finset.prod_add]
  simp

/-- The exact finite product formula for a multiplicative tilt. -/
theorem bernoulliSubsetMass_tilt {α : Type*} [DecidableEq α]
    (P : Finset α) (q v : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, (1 - q p + q p * v p) := by
  calc
    _ = ∑ S ∈ P.powerset,
        (∏ p ∈ S, q p * v p) * ∏ p ∈ P \ S, (1 - q p) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib]
      unfold bernoulliSubsetMass
      ring
    _ = _ := by rw [← Finset.prod_add]; congr 1; ext p; ring

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

theorem singularFactor_one_le {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    1 ≤ singularFactor C j := by
  exact Finset.one_le_prod (fun p _ => le_add_of_nonneg_right (div_nonneg hC (Nat.cast_nonneg p)))

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

theorem regularCoefficientWeight_nonneg (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    0 ≤ regularCoefficientWeight B L τ C n := by
  unfold regularCoefficientWeight
  split_ifs
  · exact coefficientWeight_nonneg _ _
  · rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationMultiplier
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's multiplier scale and negligible diagonal cap -/

namespace JointDickman
open Filter
open scoped Topology

theorem amplificationMultiplier_comparable : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
      (B : ℝ) ^ (8/25 : ℝ) / 2 ≤ amplificationMultiplier B ∧
      (amplificationMultiplier B : ℝ) ≤ (B : ℝ) ^ (8/25 : ℝ) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8/25)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hp.eventually_ge_atTop 2] with B hB
  change 2 ≤ (B : ℝ) ^ (8/25 : ℝ) at hB
  have hl := Nat.lt_floor_add_one ((B : ℝ) ^ (8/25 : ℝ))
  have hpos : 0 < amplificationMultiplier B := by
    apply Nat.floor_pos.mpr
    linarith
  exact ⟨hpos,by dsimp [amplificationMultiplier] <;> linarith,
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)⟩

theorem amplificationMultiplier_valid : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
      (amplificationMultiplier B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) := by
  have hlim := ((isLittleO_rpow_exp_pos_mul_atTop (8/25 : ℝ)
    (by norm_num : (0 : ℝ) < 1/10)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  filter_upwards [amplificationMultiplier_comparable,
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hB he
  refine ⟨hB.1, hB.2.2.trans ?_⟩
  exact (div_le_one (Real.exp_pos _)).mp he

theorem power_div_amplificationMultiplier {r : ℝ} (hr : r < 8/25) :
    Tendsto (fun B : ℕ => (B : ℝ)^r / amplificationMultiplier B) atTop (nhds 0) := by
  have hp := (power_div_power_tendsto_zero hr).comp tendsto_natCast_atTop_atTop
  have hu : ∀ᶠ B : ℕ in atTop,
      (B : ℝ)^r / amplificationMultiplier B ≤ 2*((B : ℝ)^r / (B : ℝ)^(8/25 : ℝ)) := by
    filter_upwards [amplificationMultiplier_comparable,eventually_gt_atTop 0] with B hB hB0
    have hpow : 0 < (B : ℝ)^(8/25 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hB0) _
    have hT : (0 : ℝ) < amplificationMultiplier B := by exact_mod_cast hB.1
    apply (div_le_iff₀ hT).mpr
    have hnon := Real.rpow_nonneg (Nat.cast_nonneg B) r
    calc
      _ = 2*((B : ℝ)^r / (B : ℝ)^(8/25 : ℝ)) * ((B : ℝ)^(8/25 : ℝ)/2) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hB.2.1 (by positivity)
  apply squeeze_zero' (Eventually.of_forall fun B => div_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) hu
  simpa using hp.const_mul 2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationSquareRate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The model's inverse-length row moment is smaller than the sampling scale -/
namespace JointDickman
open Filter
open scoped Topology

theorem amplification_inverse_square_rate (C : ℝ) :
    ∀ᶠ B : ℕ in atTop, C/(amplificationMultiplier B : ℝ) ≤ (B : ℝ)^(-(21/100 : ℝ)) := by
  have ht := (power_div_amplificationMultiplier (by norm_num : (21/100 : ℝ) < 8/25)).const_mul C
  have ht' : Tendsto (fun B : ℕ => C*((B : ℝ)^(21/100 : ℝ)/amplificationMultiplier B))
      atTop (𝓝 0) := by simpa only [mul_zero] using ht
  filter_upwards [ht'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with B hb hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hp : 0 < (B : ℝ)^(21/100 : ℝ) := Real.rpow_pos_of_pos hBp _
  rw [Real.rpow_neg hBp.le,← one_div]
  apply (le_div_iff₀ hp).mpr
  calc
    _ = C*((B : ℝ)^(21/100 : ℝ)/amplificationMultiplier B) := by ring
    _ ≤ 1 := hb

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateRootGeometry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniqueness of a representation at a fixed pair of endpoints -/

namespace JointDickman
open Finset

open Classical in
theorem mem_blockCandidatePool {B L M : ℕ} {τ C : ℝ} {S : Fin M → Finset ℕ}
    {e : BlockCandidateIndex M} :
    e ∈ blockCandidatePool B L M τ C S ↔
      e.2.1 ∈ endpointSplits B L τ C (S e.1.1) ∧
      e.2.2 ∈ endpointSplits B L τ C (S e.1.2) := by
  unfold blockCandidatePool
  constructor
  · intro h
    obtain ⟨ik,_,h⟩ := mem_biUnion.mp h
    obtain ⟨ab,hab,he⟩ := mem_image.mp h
    subst e
    simpa only [Finset.product_eq_sprod,mem_product] using hab
  · rintro ⟨hlo,hhi⟩
    apply mem_biUnion.mpr
    refine ⟨e.1,mem_univ _,mem_image.mpr ⟨e.2,?_,by cases e; rfl⟩⟩
    simpa only [Finset.product_eq_sprod,mem_product] using And.intro hlo hhi

open Classical in
theorem mem_blockCandidates {B L T H M : ℕ} {τ C : ℝ} {S : Fin M → Finset ℕ}
    {e : BlockCandidateIndex M} :
    e ∈ blockCandidates B L T H M τ C S ↔
      (e.2.1 ∈ endpointSplits B L τ C (S e.1.1) ∧
        e.2.2 ∈ endpointSplits B L τ C (S e.1.2)) ∧
      BlockCandidateAdmissible B L T H τ C e := by
  simp only [blockCandidates,mem_filter,mem_blockCandidatePool]

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingSkeleton
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A small-column sampling skeleton

This is the deterministic part of `sampling-skeleton` in the manuscript.
Sampling with replacement allows repeated columns; their multiplicities are
retained in the row response.  The number of distinct columns is at most the
sample size.  No probabilistic or cut-approximation hypothesis is assumed.
-/

open scoped BigOperators
open Finset

namespace JointDickman

attribute [local instance] Classical.propDecidable

theorem mul_responseSign (x : ℝ) : x * responseSign x = |x| := by
  unfold responseSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem responseSign_pos_mul {a : ℝ} (ha : 0 < a) (x : ℝ) :
    responseSign (a * x) = responseSign x := by
  simp [responseSign, mul_nonneg_iff_of_pos_left ha]

/-- A mistaken best response costs at most twice its prediction error. -/
theorem responseSign_loss (x y : ℝ) :
    |x| - x * responseSign y ≤ 2 * |x - y| := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · simp [responseSign, hy, abs_of_nonneg hx, abs_nonneg]
  · rw [responseSign, ite_eq_right hy, abs_of_nonneg hx,
      abs_of_nonneg (sub_nonneg.mpr (le_trans (le_of_not_ge hy) hx))]
    linarith
  · rw [responseSign, ite_eq_left hy, abs_of_neg (lt_of_not_ge hx),
      abs_of_nonpos (sub_nonpos.mpr (le_trans (le_of_not_ge hx) hy))]
    linarith
  · simp [responseSign, hy, abs_of_neg (lt_of_not_ge hx), abs_nonneg]

theorem sum_abs_le_sqrt_card_mul_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, |f i|) ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι)
    (fun _ => (1 : ℝ)) (fun i => |f i|)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one,
    sq_abs] at h
  exact (Real.le_sqrt (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).2 h

/-- An L² approximation to the row sums gives an L¹ best-response loss. -/
theorem sum_responseSign_loss {ι : Type*} [Fintype ι] (r q : ι → ℝ) :
    (∑ i, |r i|) ≤ (∑ i, r i * responseSign (q i)) +
      2 * Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, (r i - q i) ^ 2) := by
  have h := sum_le_sum (s := (univ : Finset ι)) (fun i _ => responseSign_loss (r i) (q i))
  rw [sum_sub_distrib, ← mul_sum] at h
  have hs := sum_abs_le_sqrt_card_mul_sum_sq (fun i => r i - q i)
  linarith

private theorem expect_coordinate_product {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (f : J → A → ℝ) :
    (𝔼 σ : J → A, ∏ j, f j (σ j)) = ∏ j, 𝔼 a : A, f j a := by
  simp only [Fintype.expect_eq_sum_div_card, prod_div_distrib, prod_const, card_univ,
    Fintype.card_fun, Nat.cast_pow]
  congr 1
  simpa using (prod_univ_sum (fun _ : J => (univ : Finset A)) f).symm

private theorem expect_coordinate {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A] [Nonempty A]
    (j : J) (f : A → ℝ) : (𝔼 σ : J → A, f (σ j)) = 𝔼 a : A, f a := by
  classical
  have h := expect_coordinate_product (fun k a => if k = j then f a else 1)
  have hl (σ : J → A) : (∏ k, if k = j then f (σ k) else 1) = f (σ j) := by simp
  have hr : (∏ k : J, 𝔼 a : A, if k = j then f a else 1) = 𝔼 a : A, f a := by
    rw [prod_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  simpa only [hl, hr] using h

private theorem expect_distinct_coordinates {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    [Nonempty A] {j k : J} (hjk : j ≠ k) (f g : A → ℝ) :
    (𝔼 σ : J → A, f (σ j) * g (σ k)) = (𝔼 a : A, f a) * 𝔼 a : A, g a := by
  classical
  let w : J → A → ℝ := fun l a => if l = j then f a else if l = k then g a else 1
  have hw (σ : J → A) : (∏ l, w l (σ l)) = f (σ j) * g (σ k) := by
    rw [Finset.prod_eq_mul_of_mem j k (mem_univ _) (mem_univ _) hjk]
    · simp [w, hjk.symm]
    · intro l _ ⟨hlj, hlk⟩
      simp [w, hlj, hlk]
  have he : (∏ l, 𝔼 a : A, w l a) = (𝔼 a : A, f a) * 𝔼 a : A, g a := by
    rw [Finset.prod_eq_mul_of_mem j k (mem_univ _) (mem_univ _) hjk]
    · simp [w, hjk.symm]
    · intro l _ ⟨hlj, hlk⟩
      simp [w, hlj, hlk]
  simpa only [hw, he] using expect_coordinate_product w

/-- Independent, centered coordinate samples have no off-diagonal terms. -/
theorem expect_sample_sum_sq {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : (𝔼 a : A, f a) = 0) :
    (𝔼 σ : J → A, (∑ j, f (σ j)) ^ 2) =
      (Fintype.card J : ℝ) * (𝔼 a : A, f a ^ 2) := by
  classical
  simp_rw [pow_two, sum_mul, mul_sum]
  rw [expect_sum_comm]
  simp_rw [expect_sum_comm]
  have hpair (j k : J) : (𝔼 σ : J → A, f (σ j) * f (σ k)) =
      if j = k then (𝔼 a : A, f a ^ 2) else 0 := by
    by_cases h : j = k
    · subst k
      simpa only [pow_two, ite_true, if_true] using
        (expect_coordinate (J := J) j (fun a => f a * f a))
    · rw [expect_distinct_coordinates h, hf, zero_mul, ite_eq_right h]
  simp_rw [hpair]
  simp [pow_two]

/-- The usual finite-population variance identity. -/
theorem expect_centered_sq {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (𝔼 a : A, (f a - (𝔼 b : A, f b)) ^ 2) =
      (𝔼 a : A, f a ^ 2) - (𝔼 a : A, f a) ^ 2 := by
  simp_rw [sub_sq, expect_add_distrib, expect_sub_distrib]
  rw [Fintype.expect_const, ← Finset.expect_mul, ← mul_expect]
  ring

/-- Mean-square error for independent uniform samples, with replacement. -/
theorem expect_sample_mean_sq_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (m : ℕ) (hm : 0 < m) :
    (𝔼 σ : Fin m → A,
      ((∑ j, f (σ j)) / m - (𝔼 a : A, f a)) ^ 2) ≤
        (𝔼 a : A, f a ^ 2) / m := by
  let μ := 𝔼 a : A, f a
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (𝔼 a : A, (f a - μ)) = 0 := by
    rw [expect_sub_distrib, Fintype.expect_const]
    exact sub_self _
  have he (σ : Fin m → A) :
      (∑ j, f (σ j)) / m - μ = (∑ j, (f (σ j) - μ)) / m := by
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  change (𝔼 σ : Fin m → A, ((∑ j, f (σ j)) / m - μ) ^ 2) ≤ _
  simp_rw [he, div_pow]
  rw [← expect_div, expect_sample_sum_sq (J := Fin m) (fun a => f a - μ) hc]
  simp only [Fintype.card_fin]
  rw [show (𝔼 a : A, (f a - μ) ^ 2) = (𝔼 a : A, f a ^ 2) - μ ^ 2 from
    expect_centered_sq f]
  calc
    _ = ((𝔼 a : A, f a ^ 2) - μ ^ 2) / m := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg μ)) hmpos.le

/-- The column estimator approximates every row simultaneously in squared error. -/
theorem exists_column_sample_sq_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : ι → ι → ℝ) (δ : ι → ℝ) (hδ : ∀ j, |δ j| = 1)
    (m : ℕ) (hm : 0 < m) :
    ∃ σ : Fin m → ι,
      (∑ i, ((∑ j, K i j * δ j) -
        (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a)) ^ 2) ≤
          (Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2 := by
  classical
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hrow (i : ι) :
      (𝔼 σ : Fin m → ι, ((∑ j, K i j * δ j) -
        (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a)) ^ 2) ≤
          (Fintype.card ι : ℝ) / m * ∑ j, K i j ^ 2 := by
    have hh := expect_sample_mean_sq_le (fun j => K i j * δ j) m hm
    have hd (j : ι) : (K i j * δ j) ^ 2 = K i j ^ 2 := by
      have hs : (δ j) ^ 2 = 1 := by nlinarith [sq_abs (δ j), hδ j]
      rw [mul_pow, hs, mul_one]
    have he (σ : Fin m → ι) :
        ((∑ j, K i j * δ j) -
          (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a)) ^ 2 =
        (Fintype.card ι : ℝ) ^ 2 *
          ((∑ a, K i (σ a) * δ (σ a)) / m -
            (𝔼 j : ι, K i j * δ j)) ^ 2 := by
      rw [Fintype.expect_eq_sum_div_card]
      field_simp
      ring
    simp_rw [he]
    rw [← mul_expect]
    refine (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq ?_
    simp_rw [hd]
    rw [Fintype.expect_eq_sum_div_card]
    field_simp
  have hmean :
      (𝔼 σ : Fin m → ι, ∑ i, ((∑ j, K i j * δ j) -
        (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a)) ^ 2) ≤
          (Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2 := by
    rw [expect_sum_comm, mul_sum]
    exact sum_le_sum (fun i _ => hrow i)
  obtain ⟨σ, _, hσ⟩ := exists_le_of_expect_le (s := (univ : Finset (Fin m → ι)))
    univ_nonempty hmean
  exact ⟨σ, hσ⟩

/-- Removing a set of indices costs at most its row and column mass. -/
theorem delete_endpoints_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (hsym : ∀ i j, K i j = K j i)
    (d : ℝ) (hrow : ∀ i, (∑ j, |K i j|) ≤ d)
    (T : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    realBilinear K f g ≤
      (∑ i ∈ univ \ T, ∑ j ∈ univ \ T, K i j * f i * g j) +
        2 * T.card * d := by
  let R := univ \ T
  have hpart (a : ι → ℝ) : (∑ i, a i) = (∑ i ∈ R, a i) + ∑ i ∈ T, a i := by
    exact (sum_sdiff (f := a) (subset_univ T)).symm
  have hterm (i j : ι) : |K i j * f i * g j| ≤ |K i j| := by
    rw [abs_mul, abs_mul]
    calc
      |K i j| * |f i| * |g j| ≤ |K i j| * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)) (hg j)
          (abs_nonneg _) (by positivity)
      _ = |K i j| := by ring
  have hremoved : (∑ i ∈ T, ∑ j, K i j * f i * g j) ≤ T.card * d := by
    calc
      _ ≤ ∑ i ∈ T, ∑ j, |K i j| := by
        exact sum_le_sum fun i _ => sum_le_sum fun j _ => (le_abs_self _).trans (hterm i j)
      _ ≤ ∑ _i ∈ T, d := sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  have hcross : (∑ i ∈ R, ∑ j ∈ T, K i j * f i * g j) ≤ T.card * d := by
    rw [sum_comm]
    calc
      _ ≤ ∑ j ∈ T, ∑ i ∈ R, |K j i| := by
        apply sum_le_sum
        intro j _
        apply sum_le_sum
        intro i _
        rw [← hsym i j]
        exact (le_abs_self _).trans (hterm i j)
      _ ≤ ∑ j ∈ T, ∑ i, |K j i| := by
        exact sum_le_sum fun j _ => sum_le_sum_of_subset_of_nonneg (subset_univ R)
          (fun _ _ _ => abs_nonneg _)
      _ ≤ ∑ _j ∈ T, d := sum_le_sum fun j _ => hrow j
      _ = _ := by simp
  have he : realBilinear K f g =
      (∑ i ∈ R, ∑ j ∈ R, K i j * f i * g j) +
      (∑ i ∈ R, ∑ j ∈ T, K i j * f i * g j) +
      (∑ i ∈ T, ∑ j, K i j * f i * g j) := by
    unfold realBilinear
    rw [hpart]
    conv_lhs => arg 1; arg 2; ext i; rw [hpart]
    rw [sum_add_distrib]
  change _ ≤ (∑ i ∈ R, ∑ j ∈ R, K i j * f i * g j) + _
  linarith

/-- A fixed column-sign vector has a small-column best response with explicit loss. -/
theorem exists_sampled_response_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K : ι → ι → ℝ) (hsym : ∀ i j, K i j = K j i)
    (d : ℝ) (hrow : ∀ i, (∑ j, |K i j|) ≤ d)
    (δ : ι → ℝ) (hδ : ∀ j, |δ j| = 1) (m : ℕ) (hm : 0 < m) :
    ∃ σ : Fin m → ι,
      (∑ i, |∑ j, K i j * δ j|) ≤
        residualColumnBound K (univ.image σ) (sampledResponse K δ σ) +
        2 * Real.sqrt ((Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2)) + 2 * m * d := by
  obtain ⟨σ, hσ⟩ := exists_column_sample_sq_le K δ hδ m hm
  refine ⟨σ, ?_⟩
  let g := sampledResponse K δ σ
  let T := univ.image σ
  have hg (i : ι) : |g i| ≤ 1 := by simp [g, sampledResponse]
  have hd : 0 ≤ d := (sum_nonneg fun _ _ => abs_nonneg _).trans (hrow (Classical.arbitrary ι))
  have hcard : (T.card : ℝ) ≤ m := by
    exact_mod_cast (show (univ.image σ).card ≤ m by simpa using card_image_le (f := σ) (s := univ))
  have hpos : 0 < (Fintype.card ι : ℝ) / m := by positivity
  have hresp : (∑ i, |∑ j, K i j * δ j|) ≤ realBilinear K g δ +
      2 * Real.sqrt ((Fintype.card ι : ℝ) *
        ((Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2)) := by
    have hl := sum_responseSign_loss (fun i => ∑ j, K i j * δ j)
      (fun i => (Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a))
    have he : (∑ i, (∑ j, K i j * δ j) *
        responseSign ((Fintype.card ι : ℝ) / m * ∑ a, K i (σ a) * δ (σ a))) =
        realBilinear K g δ := by
      simp only [responseSign_pos_mul hpos, realBilinear, g, sampledResponse, sum_mul]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    rw [he] at hl
    have hroot := Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hσ (Nat.cast_nonneg (Fintype.card ι)))
    linarith
  have hdelete := delete_endpoints_bound K hsym d hrow T g δ hg (fun j => (hδ j).le)
  have hremaining : (∑ i ∈ univ \ T, ∑ j ∈ univ \ T, K i j * g i * δ j) ≤
      residualColumnBound K T g := by
    rw [sum_comm]
    apply sum_le_sum
    intro j _
    rw [← sum_mul]
    calc
      (∑ i ∈ univ \ T, K i j * g i) * δ j ≤
          |(∑ i ∈ univ \ T, K i j * g i) * δ j| := le_abs_self _
      _ = |∑ i ∈ univ \ T, K i j * g i| := by rw [abs_mul, hδ, mul_one]
  dsimp only [T, g] at hdelete hremaining ⊢
  nlinarith [mul_le_mul_of_nonneg_right hcard hd]

/-- A single sampled response controls every sign cut of a symmetric matrix.
The witness depends only on the matrix and uses at most `m` distinct columns. -/
theorem exists_small_column_skeleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K : ι → ι → ℝ) (hsym : ∀ i j, K i j = K j i)
    (d : ℝ) (hrow : ∀ i, (∑ j, |K i j|) ≤ d) (m : ℕ) (hm : 0 < m) :
    ∃ δ : ι → Bool, ∃ σ : Fin m → ι,
      (univ.image σ).card ≤ m ∧ ∀ s t : ι → Bool,
        |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤
          residualColumnBound K (univ.image σ)
            (sampledResponse K (fun j => cutSign (δ j)) σ) +
          2 * Real.sqrt ((Fintype.card ι : ℝ) *
            ((Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2)) + 2 * m * d := by
  classical
  let F : (ι → Bool) → ℝ := fun t => ∑ i, |∑ j, K i j * cutSign (t j)|
  obtain ⟨δ, _, hmax⟩ := (univ : Finset (ι → Bool)).exists_max_image F univ_nonempty
  obtain ⟨σ, hσ⟩ := exists_sampled_response_bound K hsym d hrow
    (fun j => cutSign (δ j)) (fun j => abs_cutSign (δ j)) m hm
  refine ⟨δ, σ, by simpa using card_image_le (f := σ) (s := univ), ?_⟩
  intro s t
  have he : realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j)) =
      ∑ i, (∑ j, K i j * cutSign (t j)) * cutSign (s i) := by
    simp only [realBilinear, sum_mul]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  calc
    _ ≤ ∑ i, |(∑ j, K i j * cutSign (t j)) * cutSign (s i)| := by
      rw [he]
      exact abs_sum_le_sum_abs _ _
    _ = F t := by simp [F, abs_mul, abs_cutSign]
    _ ≤ F δ := hmax t (mem_univ _)
    _ ≤ _ := hσ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingConcentration
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concentration after restriction to a common good event

The extension used in the manuscript's sampling argument is constructed
explicitly from a finite good set. The only concentration hypothesis below
is the uniform-constant finite-product specialization of McDiarmid's
published bounded-differences inequality.
-/

open Finset
open scoped BigOperators

namespace JointDickman

section Extension

variable {ι A : Type*} [Fintype ι] [DecidableEq A]

theorem goodSetExtension_le (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) (c L : ℝ) (x : ι → A) :
    goodSetExtension G hG f c L x ≤ L := min_le_left _ _

theorem goodSetExtension_eq (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) {c L : ℝ}
    (hlip : ∀ x ∈ G, ∀ y ∈ G, |f x - f y| ≤ c * hammingDist x y)
    (hupper : ∀ x ∈ G, f x ≤ L) {x : ι → A} (hx : x ∈ G) :
    goodSetExtension G hG f c L x = f x := by
  have hlow : f x ≤ G.inf' hG (fun y => f y + c * hammingDist x y) := by
    apply Finset.le_inf'
    intro y hy
    have h := (le_abs_self (f x - f y)).trans (hlip x hx y hy)
    linarith
  have hhigh : G.inf' hG (fun y => f y + c * hammingDist x y) ≤ f x := by
    calc
      _ ≤ f x + c * (hammingDist x x : ℝ) :=
        Finset.inf'_le (fun y => f y + c * (hammingDist x y : ℝ)) hx
      _ = f x := by simp
  unfold goodSetExtension
  rw [le_antisymm hhigh hlow, min_eq_right (hupper x hx)]

private theorem min_upper_add {L a b r : ℝ} (hr : 0 ≤ r) (hab : a ≤ b + r) :
    min L a ≤ min L b + r := by
  by_cases h : L ≤ b
  · rw [min_eq_left h]
    exact (min_le_left L a).trans (le_add_of_nonneg_right hr)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right L a).trans hab

theorem goodSetExtension_lipschitz (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) {c : ℝ} (hc : 0 ≤ c) (L : ℝ) (x y : ι → A) :
    |goodSetExtension G hG f c L x - goodSetExtension G hG f c L y| ≤
      c * hammingDist x y := by
  have hone (x y : ι → A) :
      G.inf' hG (fun z => f z + c * hammingDist x z) ≤
        G.inf' hG (fun z => f z + c * hammingDist y z) + c * hammingDist x y := by
    suffices h : G.inf' hG (fun z => f z + c * hammingDist x z) -
        c * hammingDist x y ≤ G.inf' hG (fun z => f z + c * hammingDist y z) by
      linarith
    apply Finset.le_inf'
    intro z hz
    have hinf := Finset.inf'_le (fun z => f z + c * (hammingDist x z : ℝ)) hz
    have htri : (hammingDist x z : ℝ) ≤ hammingDist x y + hammingDist y z := by
      exact_mod_cast hammingDist_triangle x y z
    have hmul := mul_le_mul_of_nonneg_left htri hc
    linarith
  have hxy := min_upper_add (L := L) (mul_nonneg hc (Nat.cast_nonneg _)) (hone x y)
  have hyx := min_upper_add (L := L) (mul_nonneg hc (Nat.cast_nonneg _)) (hone y x)
  rw [hammingDist_comm y x] at hyx
  unfold goodSetExtension
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Extension

section FiniteProbability

variable {Ω : Type*} [Fintype Ω]

theorem finiteProbability_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {E F : Ω → Prop} (hEF : ∀ x, E x → F x) :
    finiteProbability w E ≤ finiteProbability w F := by
  classical
  apply sum_le_sum
  intro x _
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · by_cases hF : F x <;> simp [hE, hF, hw x]

theorem finiteProbability_union_le {J : Type*} [Fintype J]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (E : J → Ω → Prop) :
    finiteProbability w (fun x => ∃ j, E j x) ≤ ∑ j, finiteProbability w (E j) := by
  classical
  unfold finiteProbability
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  by_cases h : ∃ j, E j x
  · obtain ⟨j, hj⟩ := h
    simp only [show (∃ j, E j x) from ⟨j, hj⟩, ite_true, if_true]
    have ht : (if E j x then w x else 0) ≤ ∑ k, if E k x then w x else 0 :=
      single_le_sum (f := fun k => if E k x then w x else 0)
        (fun k _ => by by_cases hk : E k x <;> simp [hk, hw x]) (mem_univ j)
    simpa [hj] using ht
  · simp only [h, ite_false, if_false]
    exact sum_nonneg (fun j _ => by by_cases hj : E j x <;> simp [hj, hw x])

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

theorem goodSetExtension_mean_le (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) {c L : ℝ}
    (hlip : ∀ x ∈ G, ∀ y ∈ G, |f x - f y| ≤ c * hammingDist x y)
    (hupper : ∀ x ∈ G, f x ≤ L) (hf : ∀ x, 0 ≤ f x)
    (w : (ι → A) → ℝ) (hw : ∀ x, 0 ≤ w x) :
    finiteExpectation w (goodSetExtension G hG f c L) ≤
      finiteExpectation w f + L * finiteProbability w (fun x => x ∉ G) := by
  have hpoint (x : ι → A) : goodSetExtension G hG f c L x ≤
      f x + L * (if x ∉ G then 1 else 0) := by
    by_cases hx : x ∈ G
    · rw [goodSetExtension_eq G hG f hlip hupper hx]
      simp [hx]
    · have hu := goodSetExtension_le G hG f c L x
      simp only [hx, not_false_eq_true, ite_eq_left, mul_one]
      linarith [hf x]
  calc
    _ ≤ ∑ x, w x * (f x + L * (if x ∉ G then 1 else 0)) := by
      exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x)
    _ = _ := by
      simp only [finiteExpectation, finiteProbability, mul_add, sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro x _
      split_ifs <;> ring

end FiniteProbability

section TailBound

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

theorem abs_clamp_sub_clamp_le (L x y : ℝ) : |min L x - min L y| ≤ |x - y| := by
  simpa using abs_min_sub_min_le_max L x L y

/-- A concentration bound valid on one common good event. The cost of the
bad event enters the mean only once, before any later union bound. -/
theorem goodSet_concentration (hMC : PublishedInputs.FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (G : Finset (ι → A)) (hG : G.Nonempty) (Z : (ι → A) → ℝ)
    {c L u a : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) (ha : 0 < a)
    (hZ : ∀ x, 0 ≤ Z x)
    (hlip : ∀ x ∈ G, ∀ y ∈ G, |Z x - Z y| ≤ c * hammingDist x y)
    (hmean : finiteExpectation (PublishedInputs.siteProductMass p) Z +
      L * finiteProbability (PublishedInputs.siteProductMass p) (fun x => x ∉ G) ≤ u)
    (hcut : u + a < L) :
    finiteProbability (PublishedInputs.siteProductMass p)
      (fun x => x ∈ G ∧ u + a < Z x) ≤
        Real.exp (-2 * a ^ 2 / ((Fintype.card ι : ℝ) * c ^ 2)) := by
  let f : (ι → A) → ℝ := fun x => min L (Z x)
  let W := goodSetExtension G hG f c L
  have hw (x : ι → A) : 0 ≤ PublishedInputs.siteProductMass p x :=
    prod_nonneg fun i _ => hp i (x i)
  have hf (x : ι → A) : 0 ≤ f x := le_min hL (hZ x)
  have hupper (x : ι → A) (_ : x ∈ G) : f x ≤ L := min_le_left _ _
  have hflips : ∀ x ∈ G, ∀ y ∈ G, |f x - f y| ≤ c * hammingDist x y := by
    intro x hx y hy
    exact (abs_clamp_sub_clamp_le L (Z x) (Z y)).trans (hlip x hx y hy)
  have hEW : finiteExpectation (PublishedInputs.siteProductMass p) W ≤ u := by
    have hext := goodSetExtension_mean_le G hG f hflips hupper hf
      (PublishedInputs.siteProductMass p) hw
    have hfZ : finiteExpectation (PublishedInputs.siteProductMass p) f ≤
        finiteExpectation (PublishedInputs.siteProductMass p) Z :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (min_le_right _ _) (hw x)
    linarith
  have hWlip : ∀ x y, |W x - W y| ≤ c * hammingDist x y :=
    goodSetExtension_lipschitz G hG f hc L
  have htail := hMC p hp hpone W c hc hWlip a ha
  refine (finiteProbability_mono _ hw ?_).trans htail
  intro x ⟨hxG, hxZ⟩
  have heq : W x = f x := goodSetExtension_eq G hG f hflips hupper hxG
  have hxf : u + a < f x := lt_min hcut hxZ
  rw [heq]
  linarith

end TailBound

section SparseKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem column_abs_sum_sub_le (K K' : ι → ι → ℝ) :
    |(∑ j, |∑ i, K i j|) - (∑ j, |∑ i, K' i j|)| ≤
      ∑ j, ∑ i, |K i j - K' i j| := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by
    rw [← sum_sub_distrib]
    exact abs_sum_le_sum_abs _ _)

/-- Only edges incident to changed coordinates contribute to the response.
The argument uses the two endpoint degree bounds directly, without a path
of intermediate good configurations. -/
theorem incident_change_mass_le (K K' H : ι → ι → ℝ) (T : Finset ι)
    (hsym : ∀ i j, H i j = H j i) (hH : ∀ i j, 0 ≤ H i j)
    (d : ℝ) (hrow : ∀ i, (∑ j, H i j) ≤ d)
    (hbound : ∀ i j, |K i j - K' i j| ≤ H i j)
    (heq : ∀ i ∉ T, ∀ j ∉ T, K i j = K' i j) :
    (∑ j, ∑ i, |K i j - K' i j|) ≤ 2 * T.card * d := by
  let b : ι → ℝ := fun i => if i ∈ T then 1 else 0
  have hterm (i j : ι) : |K i j - K' i j| ≤ H i j * b i + H i j * b j := by
    by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
    · simp only [b, hi, hj, ite_eq_left, mul_one]
      linarith [hbound i j, hH i j]
    · simpa [b, hi, hj]
        using hbound i j
    · simpa [b, hi, hj]
        using hbound i j
    · simp [b, hi, hj, heq i hi j hj]
  have hfirst : (∑ j, ∑ i, H i j * b i) ≤ T.card * d := by
    rw [sum_comm]
    simp_rw [← sum_mul]
    calc
      _ = ∑ i ∈ T, ∑ j, H i j := by simp [b]
      _ ≤ ∑ _i ∈ T, d := sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  have hsecond : (∑ j, ∑ i, H i j * b j) ≤ T.card * d := by
    simp_rw [← sum_mul]
    calc
      _ = ∑ j ∈ T, ∑ i, H i j := by simp [b]
      _ = ∑ j ∈ T, ∑ i, H j i := by simp_rw [hsym]
      _ ≤ ∑ _j ∈ T, d := sum_le_sum fun j _ => hrow j
      _ = _ := by simp
  have hs := sum_le_sum (s := (univ : Finset ι))
    (fun j _ => sum_le_sum (s := (univ : Finset ι)) (fun i _ => hterm i j))
  simp only [sum_add_distrib] at hs
  linarith

variable {A : Type*} [DecidableEq A]

theorem siteColumnResponse_lipschitz_on_good
    (E H : ι → ι → A → A → ℝ) (g : ι → A → ℝ)
    (hsym : ∀ i j a b, H i j a b = H j i b a)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    (hg : ∀ i a, |g i a| ≤ 1) (d : ℝ) (x y : ι → A)
    (hx : ∀ i, (∑ j, H i j (x i) (x j)) ≤ d)
    (hy : ∀ i, (∑ j, H i j (y i) (y j)) ≤ d) :
    |siteColumnResponse E g x - siteColumnResponse E g y| ≤
      (4 * d) * hammingDist x y := by
  let K : ι → ι → ℝ := fun i j => E i j (x i) (x j) * g i (x i)
  let K' : ι → ι → ℝ := fun i j => E i j (y i) (y j) * g i (y i)
  let V : ι → ι → ℝ := fun i j => H i j (x i) (x j) + H i j (y i) (y j)
  let T : Finset ι := univ.filter (fun i => x i ≠ y i)
  have hV (i j : ι) : 0 ≤ V i j := add_nonneg
    ((abs_nonneg _).trans (hdom i j (x i) (x j)))
    ((abs_nonneg _).trans (hdom i j (y i) (y j)))
  have hrow (i : ι) : (∑ j, V i j) ≤ 2 * d := by
    simp only [V, sum_add_distrib]
    linarith [hx i, hy i]
  have hmul (i j : ι) (a b : A) : |E i j a b * g i a| ≤ H i j a b := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left (hg i a) (abs_nonneg _)).trans_eq (mul_one _)).trans
      (hdom i j a b)
  have hbound (i j : ι) : |K i j - K' i j| ≤ V i j :=
    (abs_sub _ _).trans (add_le_add (hmul i j (x i) (x j)) (hmul i j (y i) (y j)))
  have heq (i : ι) (hi : i ∉ T) (j : ι) (hj : j ∉ T) : K i j = K' i j := by
    have hei : x i = y i := by simpa [T] using hi
    have hej : x j = y j := by simpa [T] using hj
    simp [K, K', hei, hej]
  have hmass := incident_change_mass_le K K' V T
    (fun i j => by simp only [V, hsym]) hV (2 * d) hrow hbound heq
  have hcol := column_abs_sum_sub_le K K'
  change |siteColumnResponse E g x - siteColumnResponse E g y| ≤ _ at hcol
  have hc : T.card = hammingDist x y := rfl
  rw [hc] at hmass
  nlinarith

end SparseKernel

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-product moments for the sampling argument

All expectations here are finite sums with the actual independent site
masses. The variance identities, conditional moments, and absolute-error
estimates are proved directly; no moment or independence input is assumed.
-/

open Finset
open scoped BigOperators
open JointDickman.PublishedInputs

namespace JointDickman

section Expectation

variable {Ω : Type*} [Fintype Ω]

theorem finiteExpectation_add (w f g : Ω → ℝ) :
    finiteExpectation w (fun x => f x + g x) = finiteExpectation w f + finiteExpectation w g := by
  simp [finiteExpectation, mul_add, sum_add_distrib]

theorem finiteExpectation_sub (w f g : Ω → ℝ) :
    finiteExpectation w (fun x => f x - g x) = finiteExpectation w f - finiteExpectation w g := by
  simp [finiteExpectation, mul_sub, sum_sub_distrib]

theorem finiteExpectation_const_mul (w f : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun x => c * f x) = c * finiteExpectation w f := by
  simp only [finiteExpectation, mul_sum]
  apply sum_congr rfl
  intro x _
  ring

theorem finiteExpectation_mul_const (w f : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun x => f x * c) = finiteExpectation w f * c := by
  simp only [finiteExpectation, sum_mul, mul_assoc]

theorem finiteExpectation_const (w : Ω → ℝ) (hw : (∑ x, w x) = 1) (c : ℝ) :
    finiteExpectation w (fun _ => c) = c := by
  rw [finiteExpectation, ← sum_mul, hw, one_mul]

theorem finiteExpectation_sum {J : Type*} [Fintype J] (w : Ω → ℝ) (f : J → Ω → ℝ) :
    finiteExpectation w (fun x => ∑ j, f j x) = ∑ j, finiteExpectation w (f j) := by
  simp only [finiteExpectation, mul_sum]
  exact sum_comm

theorem finiteExpectation_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) : finiteExpectation w f ≤ finiteExpectation w g := by
  exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hw x)

theorem finiteExpectation_abs_le_sqrt_sq (w f : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1) :
    finiteExpectation w (fun x => |f x|) ≤ Real.sqrt (finiteExpectation w (fun x => f x ^ 2)) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset Ω)
    (f := w) (g := fun x => w x * f x ^ 2) (r := fun x => w x * |f x|)
    (fun x _ => hw x) (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => by rw [mul_pow, sq_abs]; ring_nf; exact le_rfl)
  rw [hwone, one_mul] at h
  exact Real.le_sqrt_of_sq_le h

theorem finiteExpectation_centered_sq (w f : Ω → ℝ) (hwone : (∑ x, w x) = 1) :
    finiteExpectation w (fun x => (f x - finiteExpectation w f) ^ 2) =
      finiteExpectation w (fun x => f x ^ 2) - (finiteExpectation w f) ^ 2 := by
  simp_rw [sub_sq, finiteExpectation_add, finiteExpectation_sub]
  rw [finiteExpectation_const w hwone, finiteExpectation_mul_const,
    finiteExpectation_const_mul]
  ring

end Expectation

section IndependentSites

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

omit [DecidableEq ι] [Fintype A] in
theorem siteProductMass_nonneg (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : ι → A) :
    0 ≤ siteProductMass p x := prod_nonneg fun i _ => hp i (x i)

/-- The finite sum-product identity supplies independence, with no probabilistic input. -/
theorem siteProduct_expectation_prod (p f : ι → A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => ∏ i, f i (x i)) =
      ∏ i, finiteExpectation (p i) (f i) := by
  simp only [finiteExpectation, siteProductMass, ← prod_mul_distrib]
  simpa using (prod_univ_sum (fun _ : ι => (univ : Finset A))
    (fun i a => p i a * f i a)).symm

theorem siteProductMass_sum (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1) :
    (∑ x, siteProductMass p x) = 1 := by
  have h := siteProduct_expectation_prod p (fun _ _ => 1)
  simpa [finiteExpectation, hpone] using h

theorem siteProduct_expectation_coordinate (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (i : ι) (f : A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => f (x i)) = finiteExpectation (p i) f := by
  classical
  let g : ι → A → ℝ := fun j a => if j = i then f a else 1
  have hl (x : ι → A) : (∏ j, g j (x j)) = f (x i) := by simp [g]
  have hr : (∏ j, finiteExpectation (p j) (g j)) = finiteExpectation (p i) f := by
    rw [prod_eq_single i]
    · simp [g]
    · intro j _ hji
      simp [g, hji, finiteExpectation, hpone]
    · simp
  simpa only [hl, hr] using siteProduct_expectation_prod p g

theorem siteProduct_expectation_pair (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) {i j : ι} (hij : i ≠ j) (f g : A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => f (x i) * g (x j)) =
      finiteExpectation (p i) f * finiteExpectation (p j) g := by
  classical
  let h : ι → A → ℝ := fun k a => if k = i then f a else if k = j then g a else 1
  have hl (x : ι → A) : (∏ k, h k (x k)) = f (x i) * g (x j) := by
    rw [prod_eq_mul_of_mem i j (mem_univ _) (mem_univ _) hij]
    · simp [h, hij.symm]
    · intro k _ ⟨hki, hkj⟩
      simp [h, hki, hkj]
  have hr : (∏ k, finiteExpectation (p k) (h k)) =
      finiteExpectation (p i) f * finiteExpectation (p j) g := by
    rw [prod_eq_mul_of_mem i j (mem_univ _) (mem_univ _) hij]
    · simp [h, hij.symm]
    · intro k _ ⟨hki, hkj⟩
      simp [h, hki, hkj, finiteExpectation, hpone]
  simpa only [hl, hr] using siteProduct_expectation_prod p h

/-- Variance of a sum of independent centered single-site functions. -/
theorem siteProduct_centered_sum_sq (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (hf : ∀ i, finiteExpectation (p i) (f i) = 0) :
    finiteExpectation (siteProductMass p) (fun x => (∑ i, f i (x i)) ^ 2) =
      ∑ i, finiteExpectation (p i) (fun a => f i a ^ 2) := by
  simp_rw [pow_two, sum_mul, mul_sum]
  rw [finiteExpectation_sum]
  simp_rw [finiteExpectation_sum]
  have hp (i j : ι) :
      finiteExpectation (siteProductMass p) (fun x => f i (x i) * f j (x j)) =
        if i = j then finiteExpectation (p i) (fun a => f i a * f i a) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true, if_true]
      exact siteProduct_expectation_coordinate p hpone i (fun a => f i a * f i a)
    · rw [siteProduct_expectation_pair p hpone hij, hf, hf, zero_mul, ite_eq_right hij]
  simp_rw [hp]
  simp

theorem siteProduct_sum_centered_sq (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p)
      (fun x => ((∑ i, f i (x i)) - ∑ i, finiteExpectation (p i) (f i)) ^ 2) =
      ∑ i, (finiteExpectation (p i) (fun a => f i a ^ 2) -
        (finiteExpectation (p i) (f i)) ^ 2) := by
  have hc (i : ι) : finiteExpectation (p i)
      (fun a => f i a - finiteExpectation (p i) (f i)) = 0 := by
    rw [finiteExpectation_sub, finiteExpectation_const _ (hpone i), sub_self]
  have he (x : ι → A) : (∑ i, f i (x i)) - ∑ i, finiteExpectation (p i) (f i) =
      ∑ i, (f i (x i) - finiteExpectation (p i) (f i)) := by rw [sum_sub_distrib]
  simp_rw [he]
  rw [siteProduct_centered_sum_sq _ _ hpone hc]
  apply sum_congr rfl
  intro i _
  exact finiteExpectation_centered_sq _ _ (hpone i)

theorem siteProduct_sum_centered_sq_le (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p)
      (fun x => ((∑ i, f i (x i)) - ∑ i, finiteExpectation (p i) (f i)) ^ 2) ≤
      ∑ i, finiteExpectation (p i) (fun a => f i a ^ 2) := by
  rw [siteProduct_sum_centered_sq p f hpone]
  exact sum_le_sum fun i _ => sub_le_self _ (sq_nonneg _)

theorem siteProduct_sum_mean (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p) (fun x => ∑ i, f i (x i)) =
      ∑ i, finiteExpectation (p i) (f i) := by
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro i _
  exact siteProduct_expectation_coordinate p hpone i (f i)

theorem siteProduct_sum_sq_le (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p) (fun x => (∑ i, f i (x i)) ^ 2) ≤
      (∑ i, finiteExpectation (p i) (f i)) ^ 2 +
        ∑ i, finiteExpectation (p i) (fun a => f i a ^ 2) := by
  have hvar := siteProduct_sum_centered_sq_le p f hpone
  have he := finiteExpectation_centered_sq (siteProductMass p)
    (fun x => ∑ i, f i (x i)) (siteProductMass_sum p hpone)
  rw [siteProduct_sum_mean p f hpone] at he
  linarith

end IndependentSites

section ConditionalSite

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

omit [Fintype ι] [Fintype A] in
theorem insertSite_restrict (k : ι) (x : ι → A) :
    insertSite k (x k) (fun i => x i) = x := by
  funext i
  by_cases hi : i = k <;> simp [insertSite, hi]

omit [Fintype A] in
theorem siteProductMass_insertSite (p : ι → A → ℝ) (k : ι) (a : A)
    (x : {i : ι // i ≠ k} → A) :
    siteProductMass p (insertSite k a x) =
      p k a * siteProductMass (fun i : {i : ι // i ≠ k} => p i) x := by
  unfold siteProductMass
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  simp

/-- Exact finite disintegration at one site; no normalization is needed. -/
theorem siteProduct_disintegrate (p : ι → A → ℝ) (k : ι) (F : (ι → A) → ℝ) :
    finiteExpectation (siteProductMass p) F =
      finiteExpectation (p k) (fun a =>
        finiteExpectation (siteProductMass (fun i : {i : ι // i ≠ k} => p i))
          (fun x => F (insertSite k a x))) := by
  classical
  unfold finiteExpectation
  calc
    _ = ∑ z : A × ({i : ι // i ≠ k} → A),
        siteProductMass p (insertSite k z.1 z.2) * F (insertSite k z.1 z.2) := by
      refine Fintype.sum_equiv (Equiv.funSplitAt k A) _ _ ?_
      intro x
      change siteProductMass p x * F x =
        siteProductMass p (insertSite k (x k) (fun i => x i)) *
          F (insertSite k (x k) (fun i => x i))
      rw [insertSite_restrict]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [siteProductMass_insertSite, mul_sum, mul_assoc]

theorem siteProduct_expectation_two (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) {k j : ι} (hkj : k ≠ j) (F : A → A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => F (x k) (x j)) =
      finiteExpectation (p k) (fun a => finiteExpectation (p j) (F a)) := by
  rw [siteProduct_disintegrate p k]
  congr 1
  funext a
  have hj : j ≠ k := hkj.symm
  have hh := siteProduct_expectation_coordinate
    (fun i : {i : ι // i ≠ k} => p i) (fun i => hpone i) ⟨j, hj⟩ (F a)
  simpa [insertSite, hj] using hh

omit [Fintype A] in
theorem siteRowSum_insertSite (K : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, K i i a a = 0) (k : ι) (a : A)
    (x : {i : ι // i ≠ k} → A) :
    siteRowSum K k (insertSite k a x) =
      ∑ j : {j : ι // j ≠ k}, K k j a (x j) := by
  unfold siteRowSum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ k]
  simp [hdiag]

/-- The conditional notation is exactly the integrated squared row used
in the manuscript; no stronger pointwise second-moment premise is hidden. -/
theorem siteRowSquareMass_eq_sum_entries (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (K : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, K i i a a = 0) (k : ι) :
    siteRowSquareMass p K k =
      ∑ j, finiteExpectation (siteProductMass p) (fun x => K k j (x k) (x j) ^ 2) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ k]
  have hz : finiteExpectation (siteProductMass p) (fun x => K k k (x k) (x k) ^ 2) = 0 := by
    simp [finiteExpectation, hdiag]
  rw [hz, zero_add]
  unfold siteRowSquareMass
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro j _
  exact (siteProduct_expectation_two p hpone (Ne.symm j.property)
    (fun a b => K k j a b ^ 2)).symm

/-- The integrated conditional variance is bounded by the integrated
squared entries. There is no uniform conditional second-moment assumption. -/
theorem siteRow_centered_sq_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) (k : ι) :
    finiteExpectation (siteProductMass p)
      (fun x => (siteRowSum K k x - siteRowMean p K k (x k)) ^ 2) ≤
        siteRowSquareMass p K k := by
  rw [siteProduct_disintegrate p k]
  unfold siteRowSquareMass
  apply finiteExpectation_mono (p k) (hp k)
  intro a
  simp only [siteRowSum_insertSite K hdiag, insertSite_self, siteRowMean]
  exact siteProduct_sum_centered_sq_le
    (fun i : {i : ι // i ≠ k} => p i) (fun j b => K k j a b) (fun i => hpone i)

theorem siteRow_abs_centered_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) (k : ι) :
    finiteExpectation (siteProductMass p)
      (fun x => |siteRowSum K k x - siteRowMean p K k (x k)|) ≤
        Real.sqrt (siteRowSquareMass p K k) := by
  exact (finiteExpectation_abs_le_sqrt_sq _ _ (siteProductMass_nonneg p hp)
    (siteProductMass_sum p hpone)).trans
      (Real.sqrt_le_sqrt (siteRow_centered_sq_le p hp hpone K hdiag k))

theorem siteRow_abs_mean_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) (k : ι) :
    finiteExpectation (siteProductMass p) (fun x => |siteRowSum K k x|) ≤
      finiteExpectation (p k) (fun a => |siteRowMean p K k a|) +
        Real.sqrt (siteRowSquareMass p K k) := by
  have htriangle (x : ι → A) : |siteRowSum K k x| ≤
      |siteRowSum K k x - siteRowMean p K k (x k)| + |siteRowMean p K k (x k)| := by
    simpa using abs_add_le (siteRowSum K k x - siteRowMean p K k (x k))
      (siteRowMean p K k (x k))
  have ht := finiteExpectation_mono (siteProductMass p) (siteProductMass_nonneg p hp) htriangle
  rw [finiteExpectation_add, siteProduct_expectation_coordinate p hpone k
    (fun a => |siteRowMean p K k a|)] at ht
  have he := siteRow_abs_centered_le p hp hpone K hdiag k
  linarith

/-- The row second moment follows from its conditional mean and the
integrated square mass, even when conditional square masses are large. -/
theorem siteRow_sq_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0)
    (k : ι) (C : ℝ) (hmean : ∀ a, |siteRowMean p K k a| ≤ C) :
    finiteExpectation (siteProductMass p) (fun x => siteRowSum K k x ^ 2) ≤
      C ^ 2 + siteRowSquareMass p K k := by
  rw [siteProduct_disintegrate p k]
  have hb (a : A) : finiteExpectation
      (siteProductMass (fun j : {j : ι // j ≠ k} => p j))
      (fun x => siteRowSum K k (insertSite k a x) ^ 2) ≤
        C ^ 2 + ∑ j : {j : ι // j ≠ k}, finiteExpectation (p j) (fun b => K k j a b ^ 2) := by
    simp only [siteRowSum_insertSite K hdiag]
    have hs := siteProduct_sum_sq_le (fun j : {j : ι // j ≠ k} => p j)
      (fun j b => K k j a b) (fun j => hpone j)
    have hm : siteRowMean p K k a ^ 2 ≤ C ^ 2 := by
      have hC : 0 ≤ C := (abs_nonneg _).trans (hmean a)
      nlinarith [sq_abs (siteRowMean p K k a),
        (sq_le_sq₀ (abs_nonneg (siteRowMean p K k a)) hC).mpr (hmean a)]
    change _ ≤ C ^ 2 + _
    change _ ≤ siteRowMean p K k a ^ 2 + _ at hs
    linarith
  calc
    _ ≤ finiteExpectation (p k) (fun a => C ^ 2 +
        ∑ j : {j : ι // j ≠ k}, finiteExpectation (p j) (fun b => K k j a b ^ 2)) :=
      finiteExpectation_mono (p k) (hp k) hb
    _ = _ := by rw [finiteExpectation_add, finiteExpectation_const _ (hpone k)]; rfl

/-- Sum of the conditional column-mean comparisons, in the normalization
before dividing by the number of sites. -/
theorem siteRow_total_abs_mean_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) :
    finiteExpectation (siteProductMass p) (fun x => ∑ k, |siteRowSum K k x|) ≤
      (∑ k, finiteExpectation (p k) (fun a => |siteRowMean p K k a|)) +
        ∑ k, Real.sqrt (siteRowSquareMass p K k) := by
  rw [finiteExpectation_sum, ← sum_add_distrib]
  exact sum_le_sum fun k _ => siteRow_abs_mean_le p hp hpone K hdiag k

theorem siteRow_multiply_test_mean (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (K : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, K i i a a = 0) (k : ι) (h : A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => siteRowSum K k x * h (x k)) =
      finiteExpectation (p k) (fun a => siteRowMean p K k a * h a) := by
  rw [siteProduct_disintegrate p k]
  congr 1
  funext a
  simp only [siteRowSum_insertSite K hdiag, insertSite_self]
  rw [finiteExpectation_mul_const,
    siteProduct_sum_mean (fun j : {j : ι // j ≠ k} => p j)
      (fun j b => K k j a b) (fun j => hpone j)]
  rfl

/-- Fixed single-site tests suffice to control the mean after the sampled
columns have been fixed. The optimizing test is the sign of the conditional
column mean, not a function of the remaining full configuration. -/
theorem siteRow_total_abs_of_tests (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) (C : ℝ)
    (htest : ∀ h : ι → A → ℝ, (∀ i a, |h i a| ≤ 1) →
      finiteExpectation (siteProductMass p) (fun x => ∑ k, siteRowSum K k x * h k (x k)) ≤ C) :
    finiteExpectation (siteProductMass p) (fun x => ∑ k, |siteRowSum K k x|) ≤
      C + ∑ k, Real.sqrt (siteRowSquareMass p K k) := by
  let h : ι → A → ℝ := fun k a => responseSign (siteRowMean p K k a)
  have hb := htest h (fun i a => by simp [h])
  have he : finiteExpectation (siteProductMass p)
      (fun x => ∑ k, siteRowSum K k x * h k (x k)) =
        ∑ k, finiteExpectation (p k) (fun a => |siteRowMean p K k a|) := by
    rw [finiteExpectation_sum]
    apply sum_congr rfl
    intro k _
    rw [siteRow_multiply_test_mean p hpone K hdiag k (h k)]
    simp only [h, mul_responseSign]
  rw [he] at hb
  have hh := siteRow_total_abs_mean_le p hp hpone K hdiag
  linarith

end ConditionalSite

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

theorem finiteProbability_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (E : Ω → Prop) :
    0 ≤ finiteProbability w E := by
  classical
  exact sum_nonneg fun x _ => by by_cases h : E x <;> simp [h, hw x]

theorem finiteExpectation_nonneg (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteExpectation w f :=
  sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

theorem finiteExpectation_indicator_cs (w A : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (B : Ω → Prop) [DecidablePred B] :
    finiteExpectation w (fun x => if B x then A x else 0) ≤
      Real.sqrt (finiteExpectation w (fun x => A x ^ 2) * finiteProbability w B) := by
  classical
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset Ω)
    (f := fun x => w x * A x ^ 2) (g := fun x => if B x then w x else 0)
    (r := fun x => w x * (if B x then A x else 0))
    (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => by by_cases hb : B x <;> simp [hb, hw x])
    (fun x _ => by
      by_cases hb : B x
      · simp only [hb, ite_true, if_true]
        ring_nf
        exact le_rfl
      · simp [hb])
  have hprob : (∑ x, if B x then w x else 0) = finiteProbability w B := by
    unfold finiteProbability
    apply sum_congr rfl
    intro x _
    by_cases hx : B x <;> simp [hx]
  rw [hprob] at h
  exact Real.le_sqrt_of_sq_le h

theorem finiteProbability_bad_family {J : Type*} [Fintype J]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (G : Ω → Prop) (E : J → Ω → Prop) :
    finiteProbability w (fun x => ¬ G x ∨ ∃ j, E j x) ≤
      finiteProbability w (fun x => ¬ G x) +
        ∑ j, finiteProbability w (fun x => G x ∧ E j x) := by
  classical
  have hs : finiteProbability w (fun x => ¬ G x ∨ ∃ j, E j x) =
      finiteProbability w (fun x => ¬ G x) +
        finiteProbability w (fun x => ∃ j, G x ∧ E j x) := by
    unfold finiteProbability
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    by_cases hg : G x <;> simp [hg]
  rw [hs]
  have hu := finiteProbability_union_le w hw (fun j x => G x ∧ E j x)
  linarith

/-- Finite Cauchy–Schwarz turns a tail estimate into an expectation estimate. -/
theorem finiteExpectation_transfer {J : Type*} [Fintype J]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1)
    (X A : Ω → ℝ) (Z : J → Ω → ℝ) (G : Ω → Prop)
    (e u V t : ℝ) (hthreshold : 0 ≤ u + e) (hV : 0 ≤ V)
    (hdom : ∀ x, X x ≤ A x)
    (hgood : ∀ x, G x → ∃ j, X x ≤ Z j x + e)
    (htail : ∀ j, finiteProbability w (fun x => G x ∧ u < Z j x) ≤ t)
    (hmoment : finiteExpectation w (fun x => A x ^ 2) ≤ V) :
    finiteExpectation w X ≤ u + e +
      Real.sqrt (V * (finiteProbability w (fun x => ¬ G x) + (Fintype.card J : ℝ) * t)) := by
  classical
  let B : Ω → Prop := fun x => ¬ G x ∨ ∃ j, u < Z j x
  have hB : finiteProbability w B ≤
      finiteProbability w (fun x => ¬ G x) + (Fintype.card J : ℝ) * t := by
    have hu := finiteProbability_bad_family w hw G (fun j x => u < Z j x)
    have hs := sum_le_sum (s := (univ : Finset J)) (fun j _ => htail j)
    simp only [sum_const, card_univ, nsmul_eq_mul] at hs
    exact hu.trans (by linarith)
  have hpoint (x : Ω) : X x ≤ u + e + (if B x then A x else 0) := by
    by_cases hb : B x
    · simp only [hb, ite_true, if_true]
      linarith [hdom x]
    · have hg : G x := by
        by_contra hng
        exact hb (Or.inl hng)
      obtain ⟨j, hj⟩ := hgood x hg
      have hz : Z j x ≤ u := by
        by_contra hzu
        exact hb (Or.inr ⟨j, lt_of_not_ge hzu⟩)
      simp only [hb, ite_false, if_false, add_zero]
      linarith
  have hE := finiteExpectation_mono w hw hpoint
  rw [finiteExpectation_add, finiteExpectation_const w hwone] at hE
  have hcs := finiteExpectation_indicator_cs w A hw B
  have hmul : finiteExpectation w (fun x => A x ^ 2) * finiteProbability w B ≤
      V * (finiteProbability w (fun x => ¬ G x) + (Fintype.card J : ℝ) * t) :=
    mul_le_mul hmoment hB (finiteProbability_nonneg w hw B) hV
  have hsqrt := Real.sqrt_le_sqrt hmul
  linarith

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

omit [DecidableEq ι] in
theorem card_columnSample (m : ℕ) :
    Fintype.card (ColumnSample (ι := ι) m) = (2 * Fintype.card ι) ^ m := by
  simp only [ColumnSample, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  rw [← Nat.mul_pow, Nat.mul_comm]

theorem kernelCutMaximum_sample_bound [Nonempty ι] (K : ι → ι → ℝ)
    (hsym : ∀ i j, K i j = K j i) (d Q : ℝ)
    (hrow : ∀ i, (∑ j, |K i j|) ≤ d) (hsquare : (∑ i, ∑ j, K i j ^ 2) ≤ Q)
    (m : ℕ) (hm : 0 < m) :
    ∃ s : ColumnSample (ι := ι) m, kernelCutMaximum K ≤ columnSampleResidual K s +
      (2 * Real.sqrt ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) / m * Q)) + 2 * m * d) := by
  obtain ⟨δ, σ, _, hσ⟩ := exists_small_column_skeleton K hsym d hrow m hm
  refine ⟨(σ, fun a => δ (σ a)), ?_⟩
  have hc := kernelCutMaximum_le K _ hσ
  have hmult : (Fintype.card ι : ℝ) *
      ((Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2) ≤
        (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) / m * Q) := by
    gcongr
  have hsqrt := Real.sqrt_le_sqrt hmult
  change kernelCutMaximum K ≤
    residualColumnBound K (univ.image σ) (sampledResponse K (fun j => cutSign (δ j)) σ) + _
  linarith

theorem kernelCutNorm_le_absolute_mass (K : ι → ι → ℝ) :
    kernelCutNorm K ≤ kernelAbsoluteMass K :=
  div_le_div_of_nonneg_right (kernelCutMaximum_le_absolute_mass K) (Nat.cast_nonneg _)

theorem kernelCutNorm_sample_bound [Nonempty ι] (K : ι → ι → ℝ)
    (hsym : ∀ i j, K i j = K j i) (d Q : ℝ)
    (hrow : ∀ i, (∑ j, |K i j|) ≤ d) (hsquare : (∑ i, ∑ j, K i j ^ 2) ≤ Q)
    (m : ℕ) (hm : 0 < m) :
    ∃ s : ColumnSample (ι := ι) m,
      kernelCutNorm K ≤ columnSampleNorm K s + samplingError (ι := ι) d Q m := by
  obtain ⟨s, hs⟩ := kernelCutMaximum_sample_bound K hsym d Q hrow hsquare m hm
  refine ⟨s, ?_⟩
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
  simpa only [kernelCutNorm, columnSampleNorm, samplingError, add_div] using hh

end CutFamily

section RandomMatrix

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Quantitative transfer from the finite family to the fully adaptive cut.
The common bad-event mass appears only once in the final error. -/
theorem randomMatrix_sampling_transfer
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1)
    (K : Ω → ι → ι → ℝ) (G : Ω → Prop) (d Q u V t : ℝ)
    (m : ℕ) (hm : 0 < m) (hV : 0 ≤ V)
    (hthreshold : 0 ≤ u + samplingError (ι := ι) d Q m)
    (hsym : ∀ x, G x → ∀ i j, K x i j = K x j i)
    (hrow : ∀ x, G x → ∀ i, (∑ j, |K x i j|) ≤ d)
    (hsquare : ∀ x, G x → (∑ i, ∑ j, K x i j ^ 2) ≤ Q)
    (htail : ∀ s : ColumnSample (ι := ι) m,
      finiteProbability w (fun x => G x ∧ u < columnSampleNorm (K x) s) ≤ t)
    (hmoment : finiteExpectation w (fun x => kernelAbsoluteMass (K x) ^ 2) ≤ V) :
    finiteExpectation w (fun x => kernelCutNorm (K x)) ≤
      u + samplingError (ι := ι) d Q m +
        Real.sqrt (V * (finiteProbability w (fun x => ¬ G x) +
          (((2 * Fintype.card ι) ^ m : ℕ) : ℝ) * t)) := by
  have hh := finiteExpectation_transfer w hw hwone
    (fun x => kernelCutNorm (K x)) (fun x => kernelAbsoluteMass (K x))
    (fun s x => columnSampleNorm (K x) s) G
    (samplingError (ι := ι) d Q m) u V t hthreshold hV
    (fun x => kernelCutNorm_le_absolute_mass (K x))
    (fun x hx => kernelCutNorm_sample_bound (K x) (hsym x hx) d Q (hrow x hx) (hsquare x hx) m hm)
    htail hmoment
  simpa only [card_columnSample] using hh

end RandomMatrix

section KernelMoments

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem finiteExpectation_div (w f : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun x => f x / c) = finiteExpectation w f / c := by
  simp only [div_eq_mul_inv, finiteExpectation_mul_const]

omit [DecidableEq ι] in
theorem kernelAbsoluteMass_sq_le_average_rows (K : ι → ι → ℝ) :
    kernelAbsoluteMass K ^ 2 ≤
      (∑ i, (∑ j, |K i j|) ^ 2) / Fintype.card ι := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι)
    (fun _ => (1 : ℝ)) (fun i => ∑ j, |K i j|)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at hcs
  unfold kernelAbsoluteMass
  calc
    _ = (∑ i, ∑ j, |K i j|) ^ 2 / (Fintype.card ι : ℝ) ^ 2 := div_pow _ _ _
    _ ≤ ((Fintype.card ι : ℝ) * ∑ i, (∑ j, |K i j|) ^ 2) /
        (Fintype.card ι : ℝ) ^ 2 := div_le_div_of_nonneg_right hcs (sq_nonneg _)
    _ = _ := by field_simp

omit [DecidableEq ι] in
theorem kernelAbsoluteMass_second_moment
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (K : Ω → ι → ι → ℝ) (V : ℝ)
    (hrow : ∀ i, finiteExpectation w (fun x => (∑ j, |K x i j|) ^ 2) ≤ V) :
    finiteExpectation w (fun x => kernelAbsoluteMass (K x) ^ 2) ≤ V := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ finiteExpectation w
        (fun x => (∑ i, (∑ j, |K x i j|) ^ 2) / Fintype.card ι) :=
      finiteExpectation_mono w hw (fun x => kernelAbsoluteMass_sq_le_average_rows (K x))
    _ = (∑ i, finiteExpectation w (fun x => (∑ j, |K x i j|) ^ 2)) /
        Fintype.card ι := by rw [finiteExpectation_div, finiteExpectation_sum]
    _ ≤ (∑ _i : ι, V) / Fintype.card ι :=
      div_le_div_of_nonneg_right (sum_le_sum (fun i _ => hrow i)) hN.le
    _ = V := by simp [hN.ne']

end KernelMoments

section SiteKernel

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A]

/-- The uniform-integrability moment required in the sampling transfer is
derived from the row-moment theorem. -/
theorem realizedSiteKernel_second_moment
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    (hdiag : ∀ i a, H i i a a = 0) (C q : ℝ)
    (hmean : ∀ i a, |siteRowMean p H i a| ≤ C)
    (hsquare : ∀ i, (∑ j, finiteExpectation (siteProductMass p)
      (fun x => H i j (x i) (x j) ^ 2)) ≤ q) :
    finiteExpectation (siteProductMass p)
      (fun x => kernelAbsoluteMass (realizedSiteKernel E x) ^ 2) ≤ C ^ 2 + q := by
  apply kernelAbsoluteMass_second_moment _ (siteProductMass_nonneg p hp)
  intro i
  have hrow : finiteExpectation (siteProductMass p) (fun x => siteRowSum H i x ^ 2) ≤
      C ^ 2 + q := by
    have hh := siteRow_sq_le p hp hpone H hdiag i C (hmean i)
    rw [siteRowSquareMass_eq_sum_entries p hpone H hdiag i] at hh
    linarith [hsquare i]
  refine (finiteExpectation_mono (siteProductMass p) (siteProductMass_nonneg p hp) ?_).trans hrow
  intro x
  have hsum : (∑ j, |realizedSiteKernel E x i j|) ≤ siteRowSum H i x :=
    sum_le_sum fun j _ => hdom i j (x i) (x j)
  exact sq_le_sq₀ (sum_nonneg fun _ _ => abs_nonneg _)
    ((sum_nonneg fun _ _ => abs_nonneg _).trans hsum) |>.mpr hsum

/-- The finite quantitative transfer for actual independent site kernels.
Only the finite family tail bound remains an explicit sampling obligation. -/
theorem siteKernel_sampling_transfer
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ) (G : (ι → A) → Prop)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    (hdiag : ∀ i a, H i i a a = 0) (hsym : ∀ i j a b, E i j a b = E j i b a)
    (C q d Q u t : ℝ) (m : ℕ) (hm : 0 < m) (hq : 0 ≤ q)
    (hmean : ∀ i a, |siteRowMean p H i a| ≤ C)
    (hsquare : ∀ i, (∑ j, finiteExpectation (siteProductMass p)
      (fun x => H i j (x i) (x j) ^ 2)) ≤ q)
    (hthreshold : 0 ≤ u + samplingError (ι := ι) d Q m)
    (hrowG : ∀ x, G x → ∀ i, (∑ j, |E i j (x i) (x j)|) ≤ d)
    (hsquareG : ∀ x, G x → (∑ i, ∑ j, E i j (x i) (x j) ^ 2) ≤ Q)
    (htail : ∀ s : ColumnSample (ι := ι) m,
      finiteProbability (siteProductMass p)
        (fun x => G x ∧ u < columnSampleNorm (realizedSiteKernel E x) s) ≤ t) :
    finiteExpectation (siteProductMass p) (fun x => kernelCutNorm (realizedSiteKernel E x)) ≤
      u + samplingError (ι := ι) d Q m +
        Real.sqrt ((C ^ 2 + q) * (finiteProbability (siteProductMass p) (fun x => ¬ G x) +
          (((2 * Fintype.card ι) ^ m : ℕ) : ℝ) * t)) := by
  apply randomMatrix_sampling_transfer _ (siteProductMass_nonneg p hp) (siteProductMass_sum p hpone)
    (realizedSiteKernel E) G d Q u (C ^ 2 + q) t m hm (add_nonneg (sq_nonneg C) hq) hthreshold
  · intro x _ i j
    exact hsym i j (x i) (x j)
  · exact hrowG
  · exact hsquareG
  · exact htail
  · exact realizedSiteKernel_second_moment p hp hpone E H hdom hdiag C q hmean hsquare

end SiteKernel

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

theorem independentPrimeSetMass_sum (B : ℕ) : (∑ R, independentPrimeSetMass B R) = 1 := by
  exact (sum_coe_sort _ _).trans (bernoulliSubsetMass_sum _ _)

theorem candidateRootWeight_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (e : BlockCandidateIndex M) (R : Finset ℕ) :
    0 ≤ candidateRootWeight B L τ C S χ e R := by
  unfold candidateRootWeight
  exact mul_nonneg (div_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
        (regularResidueWeight_nonneg _ _ _ _ _))
        (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
          (regularResidueWeight_nonneg _ _ _ _ _)))
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
        (regularResidueWeight_nonneg _ _ _ _ _))) (Nat.cast_nonneg B)) (hχ e)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IndependentRootMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem regularResidueWeight_le_base (B L : ℕ) (τ C : ℝ) (S : Finset ℕ) :
    regularResidueWeight B L τ C S ≤ residueBaseWeight B S := by
  unfold regularResidueWeight
  split_ifs
  · exact le_rfl
  · unfold residueBaseWeight
    exact mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _) (by positivity)

theorem independent_root_base_mean (B : ℕ) :
    finiteExpectation (independentPrimeSetMass B) (fun R => residueBaseWeight B R.val) =
      auxiliaryRatio B^(1/2 : ℝ)*primeNormalizer (auxiliaryPrimes B) (1/2) := by
  have he := bernoulliSubsetMass_tilt (auxiliaryPrimes B)
    (fun p => 1/(p : ℝ)) (fun _ => (1/2 : ℝ))
  simp only [prod_const] at he
  have hlocal (p : ℕ) : 1-1/(p : ℝ)+1/(p : ℝ)*(1/2) = 1-(1/2)/(p : ℝ) := by ring
  simp_rw [hlocal] at he
  unfold finiteExpectation independentPrimeSetMass
  change (∑ x : (auxiliaryPrimes B).powerset,
    (fun R : Finset ℕ => bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R *
      residueBaseWeight B R) x.val) = _
  calc
    _ = ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*residueBaseWeight B R :=
      Finset.sum_coe_sort _ _
    _ = auxiliaryRatio B^(1/2 : ℝ)*
        ∑ R ∈ (auxiliaryPrimes B).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*(1/2 : ℝ)^R.card := by
      rw [mul_sum]
      apply sum_congr rfl
      intro R _
      unfold residueBaseWeight
      ring
    _ = _ := by rw [he]; rfl

theorem independentRootMean_nonneg (B L : ℕ) (τ C : ℝ) :
    0 ≤ independentRootMean B L τ C :=
  finiteExpectation_nonneg _ _ (independentPrimeSetMass_nonneg B)
    (fun R => regularResidueWeight_nonneg B L τ C R.val)

/-- Only reciprocal-prime Mertens is used to bound the root mean, uniformly
in all truncation parameters. -/
theorem independentRootMean_bounded (hM : PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L : ℕ) (τ C : ℝ),
      independentRootMean B L τ C ≤ K := by
  let K : ℝ := (4 : ℝ)^(-(1/2 : ℝ))+1
  refine ⟨K,by dsimp [K] <;> positivity,?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1/2) (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (Iio_mem_nhds (show (4 : ℝ)^(-(1/2 : ℝ)) < K by
    dsimp [K] <;> linarith))] with B hB
  intro L τ C
  calc
    _ ≤ finiteExpectation (independentPrimeSetMass B) (fun R => residueBaseWeight B R.val) :=
      finiteExpectation_mono _ (independentPrimeSetMass_nonneg B)
        (fun R => regularResidueWeight_le_base B L τ C R.val)
    _ = auxiliaryRatio B^(1/2 : ℝ)*primeNormalizer (auxiliaryPrimes B) (1/2) :=
      independent_root_base_mean B
    _ ≤ K := by simpa only [mul_comm] using hB.le

/-- Averaging the sixth factor produces precisely the scalar k_B in
manuscript equation (20). -/
theorem candidateMeanWeight_eq {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (e : BlockCandidateIndex M) :
    candidateMeanWeight B L τ C S χ e =
      (regularCoefficientWeight B L τ C (candidateLow e)*
        regularResidueWeight B L τ C (S e.1.1 \ e.2.1)*
        (regularCoefficientWeight B L τ C (candidateHigh e)*
          regularResidueWeight B L τ C (S e.1.2 \ e.2.2))*
        regularCoefficientWeight B L τ C (candidateQuotient e))/(B : ℝ)*χ e*
          independentRootMean B L τ C := by
  unfold candidateMeanWeight independentRootMean finiteExpectation candidateRootWeight
  rw [mul_sum]
  apply sum_congr rfl
  intro R _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidatePairSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The latent kernel as a local sum over its two endpoint splits -/

namespace JointDickman
open Finset

open Classical in
theorem candidate_pair_sum {M : ℕ} (B L T H : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (w : BlockCandidateIndex M → ℝ) (i k : Fin M) :
    (∑ e ∈ blockCandidates B L T H M τ C S,
      if e.1 = (i,k) then w e else 0) =
      ∑ A ∈ endpointSplits B L τ C (S i),
        ∑ D ∈ endpointSplits B L τ C (S k),
          if BlockCandidateAdmissible B L T H τ C ((i,k),(A,D))
          then w ((i,k),(A,D)) else 0 := by
  rw [← sum_filter]
  let J := ((endpointSplits B L τ C (S i)).product
    (endpointSplits B L τ C (S k))).filter
      (fun ab => BlockCandidateAdmissible B L T H τ C ((i,k),ab))
  have heq : (∑ e ∈ (blockCandidates B L T H M τ C S).filter (fun e => e.1 = (i,k)), w e) =
      ∑ ab ∈ J, w ((i,k),ab) := by
    apply sum_bij (fun e _ => e.2)
    · intro e he
      obtain ⟨he,hpair⟩ := mem_filter.mp he
      obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
      apply mem_filter.mpr
      constructor
      · simp only [Finset.product_eq_sprod,mem_product]
        simpa only [hpair] using hs
      · have heq : e = ((i,k),e.2) := Prod.ext hpair rfl
        exact heq ▸ ha
    · intro e he f hf hef
      have hepair := (mem_filter.mp he).2
      have hfpair := (mem_filter.mp hf).2
      exact Prod.ext (hepair.trans hfpair.symm) hef
    · intro ab hab
      obtain ⟨hs,ha⟩ := mem_filter.mp hab
      refine ⟨((i,k),ab),?_,rfl⟩
      apply mem_filter.mpr
      refine ⟨mem_blockCandidates.mpr ⟨?_,ha⟩,rfl⟩
      simpa only [Finset.product_eq_sprod,mem_product] using hs
    · intro e he
      exact congrArg w (Prod.ext (mem_filter.mp he).2 rfl)
  rw [heq]
  dsimp [J]
  rw [sum_filter,sum_product]

open Classical in
/-- For i<k only the forward orientation contributes. -/
theorem latentCandidateKernel_pair {M : ℕ} (B L T H : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (hik : i < k) :
    latentCandidateKernel B L T H M τ C S χ i k =
      ∑ A ∈ endpointSplits B L τ C (S i),
        ∑ D ∈ endpointSplits B L τ C (S k),
          if BlockCandidateAdmissible B L T H τ C ((i,k),(A,D))
          then candidateMeanWeight B L τ C S χ ((i,k),(A,D)) else 0 := by
  classical
  rw [← candidate_pair_sum B L T H τ C S (candidateMeanWeight B L τ C S χ) i k]
  unfold latentCandidateKernel candidateMatrix
  change (∑ e : blockCandidates B L T H M τ C S,
    (fun e : BlockCandidateIndex M =>
      (if i = e.1.1 then if k = e.1.2 then candidateMeanWeight B L τ C S χ e else 0 else 0)+
      (if i = e.1.2 then if k = e.1.1 then candidateMeanWeight B L τ C S χ e else 0 else 0)) e.val) = _
  trans ∑ e ∈ blockCandidates B L T H M τ C S,
    ((if i = e.1.1 then if k = e.1.2 then candidateMeanWeight B L τ C S χ e else 0 else 0)+
      (if i = e.1.2 then if k = e.1.1 then candidateMeanWeight B L τ C S χ e else 0 else 0))
  · exact sum_coe_sort (blockCandidates B L T H M τ C S)
      (fun (e : BlockCandidateIndex M) =>
        (if i = e.1.1 then if k = e.1.2 then candidateMeanWeight B L τ C S χ e else 0 else 0)+
        (if i = e.1.2 then if k = e.1.1 then candidateMeanWeight B L τ C S χ e else 0 else 0))
  · apply sum_congr rfl
    intro e he
    have heord := (mem_blockCandidates.mp he).2.1
    have hback : ¬(i = e.1.2 ∧ k = e.1.1) := by
      rintro ⟨hi,hk⟩
      rw [← hi,← hk] at heord
      exact (not_lt_of_ge hik.le) heord
    have hpair : e.1 = (i,k) ↔ i = e.1.1 ∧ k = e.1.2 := by
      simp only [Prod.ext_iff]
      exact and_congr eq_comm eq_comm
    by_cases hi : i = e.1.1 <;> by_cases hk : k = e.1.2 <;>
      by_cases hi' : i = e.1.2 <;> by_cases hk' : k = e.1.1 <;>
      simp_all only [ite_true, if_true,ite_false, if_false,add_zero,not_true_eq_false,and_self,
        and_false,false_and,not_false_eq_true]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SiteDegreeTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional row variance gives a common degree event -/

namespace JointDickman
open Finset Classical
open PublishedInputs

/-- Markov's inequality for the finite nonnegative weights used here. -/
theorem finiteProbability_markov {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x)
    {t : ℝ} (ht : 0 < t) :
    finiteProbability w (fun x => t < f x) ≤ finiteExpectation w f/t := by
  unfold finiteProbability finiteExpectation
  rw [sum_div]
  apply sum_le_sum
  intro x _
  split_ifs with hx
  · have hh : 1 ≤ f x/t := (le_div_iff₀ ht).mpr (by linarith)
    simpa only [mul_one,mul_div_assoc] using mul_le_mul_of_nonneg_left hh (hw x)
  · exact div_nonneg (mul_nonneg (hw x) (hf x)) ht.le

/-- The mean is bounded for every row type, but the variance bound is
integrated over that type. This is sufficient for the degree tail. -/
theorem siteRow_degree_tail {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0)
    (i : ι) {C d : ℝ} (hgap : C < d)
    (hmean : ∀ a, |siteRowMean p K i a| ≤ C) :
    finiteProbability (siteProductMass p) (fun x => d < siteRowSum K i x) ≤
      siteRowSquareMass p K i/(d-C)^2 := by
  have hden : 0 < (d-C)^2 := sq_pos_of_pos (sub_pos.mpr hgap)
  let g := fun x => siteRowSum K i x-siteRowMean p K i (x i)
  have hsub : finiteProbability (siteProductMass p) (fun x => d < siteRowSum K i x) ≤
      finiteProbability (siteProductMass p) (fun x => (d-C)^2 < (g x)^2) := by
    apply finiteProbability_mono _ (siteProductMass_nonneg p hp)
    intro x hx
    have hm : siteRowMean p K i (x i) ≤ C := (le_abs_self _).trans (hmean _)
    have hg : d-C < g x := by dsimp only [g] <;> linarith
    nlinarith [sub_pos.mpr hgap]
  refine hsub.trans ((finiteProbability_markov (siteProductMass p) (fun x => (g x)^2)
    (siteProductMass_nonneg p hp) (fun _ => sq_nonneg _) hden).trans ?_)
  exact div_le_div_of_nonneg_right (siteRow_centered_sq_le p hp hpone K hdiag i) hden.le

/-- Union over all rows pays only the number of positions. -/
theorem siteDegree_bad_probability {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0)
    {C d q : ℝ} (hgap : C < d)
    (hmean : ∀ i a, |siteRowMean p K i a| ≤ C)
    (hsquare : ∀ i, siteRowSquareMass p K i ≤ q) :
    finiteProbability (siteProductMass p) (fun x => ¬ ∀ i, siteRowSum K i x ≤ d) ≤
      (Fintype.card ι : ℝ)*q/(d-C)^2 := by
  have hden : 0 ≤ (d-C)^2 := sq_nonneg _
  have he : (fun x : ι → A => ¬ ∀ i, siteRowSum K i x ≤ d) =
      (fun x => ∃ i, d < siteRowSum K i x) := by funext x; simp only [not_forall,not_le]
  rw [he]
  calc
    _ ≤ ∑ i, finiteProbability (siteProductMass p) (fun x => d < siteRowSum K i x) :=
      finiteProbability_union_le _ (siteProductMass_nonneg p hp) _
    _ ≤ ∑ _i : ι, q/(d-C)^2 := sum_le_sum (fun i _ =>
      (siteRow_degree_tail p hp hpone K hdiag i hgap (hmean i)).trans
        (div_le_div_of_nonneg_right (hsquare i) hden))
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SiteGoodEvent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single good event for degrees and total square mass -/

namespace JointDickman
open Finset Classical
open PublishedInputs

theorem finiteProbability_or_le {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (E F : Ω → Prop) :
    finiteProbability w (fun x => E x ∨ F x) ≤ finiteProbability w E+finiteProbability w F := by
  unfold finiteProbability
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp [he,hf,hw x]

theorem siteTotalSquare_expectation {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) :
    finiteExpectation (siteProductMass p) (siteTotalSquare K) = ∑ i, siteRowSquareMass p K i := by
  unfold siteTotalSquare
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro i _
  rw [finiteExpectation_sum,siteRowSquareMass_eq_sum_entries p hpone K hdiag i]

theorem siteTotalSquare_bad_probability {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0)
    {q Q : ℝ} (hQ : 0 < Q) (hsquare : ∀ i, siteRowSquareMass p K i ≤ q) :
    finiteProbability (siteProductMass p) (fun x => Q < siteTotalSquare K x) ≤
      (Fintype.card ι : ℝ)*q/Q := by
  refine (finiteProbability_markov (siteProductMass p) (siteTotalSquare K)
    (siteProductMass_nonneg p hp) (fun _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) hQ).trans ?_
  rw [siteTotalSquare_expectation p hpone K hdiag]
  exact div_le_div_of_nonneg_right
    ((sum_le_sum (fun i _ => hsquare i)).trans_eq (by simp)) hQ.le

theorem siteKernelGood_bad_probability {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEdiag : ∀ i a, E i i a a = 0) (hHdiag : ∀ i a, H i i a a = 0)
    {C d q Q : ℝ} (hgap : C < d) (hQ : 0 < Q)
    (hmean : ∀ i a, |siteRowMean p H i a| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q)
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q) :
    finiteProbability (siteProductMass p) (fun x => ¬ SiteKernelGood E H d Q x) ≤
      (Fintype.card ι : ℝ)*q/(d-C)^2+(Fintype.card ι : ℝ)*q/Q := by
  have he : (fun x => ¬ SiteKernelGood E H d Q x) =
      (fun x => (¬ ∀ i, siteRowSum H i x ≤ d) ∨ Q < siteTotalSquare E x) := by
    funext x
    simp only [SiteKernelGood,not_and_or,not_le]
  rw [he]
  exact (finiteProbability_or_le _ (siteProductMass_nonneg p hp) _ _).trans
    (add_le_add (siteDegree_bad_probability p hp hpone H hHdiag hgap hmean hsquareH)
      (siteTotalSquare_bad_probability p hp hpone E hEdiag hQ hsquareE))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FrozenSiteLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning on a fixed collection of sampled sites -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

omit [Fintype ι] [Fintype A] in
theorem frozenSiteMass_nonneg (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (J : Finset ι) (t : ι → A) : ∀ i a, 0 ≤ frozenSiteMass p J t i a := by
  intro i a
  unfold frozenSiteMass
  split_ifs <;> first | positivity | exact hp i a

omit [Fintype ι] in
theorem frozenSiteMass_sum (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1)
    (J : Finset ι) (t : ι → A) : ∀ i, ∑ a, frozenSiteMass p J t i a = 1 := by
  intro i
  by_cases hi : i ∈ J <;> simp [frozenSiteMass,hi,hpone]

theorem frozenSiteMass_average (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1)
    (J : Finset ι) (x : ι → A) :
    (∑ t, siteProductMass p t * siteProductMass (frozenSiteMass p J t) x) =
      siteProductMass p x := by
  simp only [siteProductMass,← prod_mul_distrib]
  unfold frozenSiteMass
  rw [← Fintype.prod_sum (fun i a => p i a *
    (if i ∈ J then if x i = a then 1 else 0 else p i (x i)))]
  apply prod_congr rfl
  intro i _
  by_cases hi : i ∈ J
  · simp [hi]
  · simp [hi,← sum_mul,hpone]

omit [Fintype A] in
theorem frozenSiteMass_support (p : ι → A → ℝ) (J : Finset ι) (t x : ι → A)
    (hx : siteProductMass (frozenSiteMass p J t) x ≠ 0) :
    ∀ i ∈ J, x i = t i := by
  intro i hi
  have hn : frozenSiteMass p J t i (x i) ≠ 0 :=
    (prod_ne_zero_iff.mp hx) i (mem_univ i)
  by_contra hne
  exact hn (by simp [frozenSiteMass,hi,hne])

/-- Averaging the conditional law recovers the original law. The test may
depend on the fixed types, provided only their sampled coordinates matter. -/
theorem frozenSiteMass_disintegrate (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (J : Finset ι)
    (F : (ι → A) → (ι → A) → ℝ)
    (hF : ∀ t x, (∀ i ∈ J, x i = t i) → F t x = F x x) :
    finiteExpectation (siteProductMass p) (fun x => F x x) =
      finiteExpectation (siteProductMass p) (fun t =>
        finiteExpectation (siteProductMass (frozenSiteMass p J t)) (F t)) := by
  unfold finiteExpectation
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  symm
  calc
    _ = ∑ t, (siteProductMass p t * siteProductMass (frozenSiteMass p J t) x) * F x x := by
      apply sum_congr rfl
      intro t _
      by_cases hx : siteProductMass (frozenSiteMass p J t) x = 0
      · simp [hx]
      · rw [hF t x (frozenSiteMass_support p J t x hx)]
        ring
    _ = _ := by rw [← sum_mul,frozenSiteMass_average p hpone]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_MaskedSiteMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deleting the sampled sites preserves the moment bounds -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

omit [Fintype ι] [Fintype A] in
theorem maskedSiteKernel_diag (J : Finset ι) (K : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, K i i a a = 0) : ∀ i a, maskedSiteKernel J K i i a a = 0 := by
  intro i a
  simp [maskedSiteKernel,hdiag]

theorem maskedSiteKernel_mean_le (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (J : Finset ι) (t : ι → A) (H : ι → ι → A → A → ℝ)
    (hH : ∀ i j a b, 0 ≤ H i j a b) {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ i a, |siteRowMean p H i a| ≤ C) :
    ∀ i a, |siteRowMean (frozenSiteMass p J t) (maskedSiteKernel J H) i a| ≤ C := by
  intro i a
  by_cases hi : i ∈ J
  · simpa [siteRowMean,maskedSiteKernel,hi,finiteExpectation] using hC
  · have hn : 0 ≤ siteRowMean (frozenSiteMass p J t) (maskedSiteKernel J H) i a := by
      apply sum_nonneg
      intro j _
      apply finiteExpectation_nonneg _ _ (frozenSiteMass_nonneg p hp J t j)
      intro b
      unfold maskedSiteKernel
      split_ifs <;> first | exact hH i j a b | rfl
    rw [abs_of_nonneg hn]
    refine le_trans ?_ ((le_abs_self _).trans (hmean i a))
    apply sum_le_sum
    intro j _
    by_cases hj : (j : ι) ∈ J
    · simp only [maskedSiteKernel,hj,not_true_eq_false,and_false,ite_false, if_false]
      simp only [finiteExpectation,mul_zero,sum_const_zero]
      exact finiteExpectation_nonneg _ _ (hp j) (fun b => hH i j a b)
    · simp only [finiteExpectation,frozenSiteMass,maskedSiteKernel,hi,hj,
        not_false_eq_true,and_self,ite_true, if_true,ite_false, if_false]
      exact le_rfl

theorem maskedSiteKernel_square_le (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (J : Finset ι) (t : ι → A) (K : ι → ι → A → A → ℝ) (i : ι) :
    siteRowSquareMass (frozenSiteMass p J t) (maskedSiteKernel J K) i ≤
      siteRowSquareMass p K i := by
  by_cases hi : i ∈ J
  · simp only [siteRowSquareMass,maskedSiteKernel,hi,not_true_eq_false,false_and,
      ite_false, if_false,zero_pow (by decide : 2 ≠ 0),finiteExpectation,mul_zero,sum_const_zero]
    exact sum_nonneg fun a _ => mul_nonneg (hp i a) (sum_nonneg fun j _ =>
      sum_nonneg fun b _ => mul_nonneg (hp j b) (sq_nonneg _))
  · unfold siteRowSquareMass
    have he : frozenSiteMass p J t i = p i := by
      funext a
      simp [frozenSiteMass,hi]
    rw [he]
    apply finiteExpectation_mono (p i) (hp i)
    intro a
    apply sum_le_sum
    intro j _
    by_cases hj : (j : ι) ∈ J
    · simp only [maskedSiteKernel,hj,not_true_eq_false,and_false,ite_false, if_false,
        zero_pow (by decide : 2 ≠ 0),finiteExpectation,mul_zero,sum_const_zero]
      exact sum_nonneg fun b _ => mul_nonneg (hp j b) (sq_nonneg _)
    · simp only [finiteExpectation,frozenSiteMass,maskedSiteKernel,hi,hj,
        not_false_eq_true,and_self,ite_true, if_true,ite_false, if_false]
      exact le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SiteTestRestriction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Single-site tests after fixing sampled coordinates -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

theorem siteProduct_unfrozen_pair (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (J : Finset ι) (t : ι → A)
    {i j : ι} (hi : i ∉ J) (hj : j ∉ J) (F : A → A → ℝ) :
    finiteExpectation (siteProductMass (frozenSiteMass p J t)) (fun x => F (x i) (x j)) =
      finiteExpectation (siteProductMass p) (fun x => F (x i) (x j)) := by
  by_cases hij : i = j
  · subst j
    rw [siteProduct_expectation_coordinate _ (frozenSiteMass_sum p hpone J t) i (fun a => F a a),
      siteProduct_expectation_coordinate _ hpone i (fun a => F a a)]
    simp only [finiteExpectation,frozenSiteMass,hi,ite_false, if_false]
  · rw [siteProduct_expectation_two _ (frozenSiteMass_sum p hpone J t) hij,
      siteProduct_expectation_two _ hpone hij]
    simp only [finiteExpectation,frozenSiteMass,hi,hj,ite_false, if_false]

theorem siteTestMean_masked_frozen (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (J : Finset ι) (t : ι → A)
    (E : ι → ι → A → A → ℝ) (g h : ι → A → ℝ) :
    siteTestMean (frozenSiteMass p J t) (maskedSiteKernel J E) g h =
      siteTestMean p E (maskedSiteTest J g) (maskedSiteTest J h) := by
  unfold siteTestMean
  rw [finiteExpectation_sum,finiteExpectation_sum]
  apply sum_congr rfl
  intro i _
  rw [finiteExpectation_sum,finiteExpectation_sum]
  apply sum_congr rfl
  intro j _
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · simp [maskedSiteKernel,maskedSiteTest,hi,hj,finiteExpectation]
  · simp [maskedSiteKernel,maskedSiteTest,hi,hj,finiteExpectation]
  · simp [maskedSiteKernel,maskedSiteTest,hi,hj,finiteExpectation]
  · simp only [maskedSiteKernel,maskedSiteTest,hi,hj,not_false_eq_true,and_self,
      ite_true, if_true,ite_false, if_false]
    exact siteProduct_unfrozen_pair p hpone J t hi hj (fun a b => E i j a b*g i a*h j b)

theorem siteTestMean_restriction_bound (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (E : ι → ι → A → A → ℝ) (C : ℝ)
    (htest : ∀ g h : ι → A → ℝ, (∀ i a, |g i a| ≤ 1) → (∀ i a, |h i a| ≤ 1) →
      siteTestMean p E g h ≤ C)
    (J : Finset ι) (t : ι → A) (g h : ι → A → ℝ)
    (hg : ∀ i a, |g i a| ≤ 1) (hh : ∀ i a, |h i a| ≤ 1) :
    siteTestMean (frozenSiteMass p J t) (maskedSiteKernel J E) g h ≤ C := by
  rw [siteTestMean_masked_frozen p hpone J t E g h]
  apply htest
  · intro i a
    by_cases hi : i ∈ J <;> simp [maskedSiteTest,hi,hg]
  · intro i a
    by_cases hi : i ∈ J <;> simp [maskedSiteTest,hi,hh]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ColumnResponseMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed single-site comparison bounds the mean column response -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

theorem siteRowSquareMass_mono (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (E F : ι → ι → A → A → ℝ)
    (hEF : ∀ i j a b, (E i j a b)^2 ≤ (F i j a b)^2) (i : ι) :
    siteRowSquareMass p E i ≤ siteRowSquareMass p F i := by
  apply finiteExpectation_mono _ (hp i)
  intro a
  apply sum_le_sum
  intro j _
  exact finiteExpectation_mono _ (hp j) (fun b => hEF i j a b)

theorem siteColumnResponse_mean_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E : ι → ι → A → A → ℝ)
    (hsym : ∀ i j a b, E i j a b = E j i b a)
    (hdiag : ∀ i a, E i i a a = 0)
    (g : ι → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1) (C q : ℝ)
    (htest : ∀ h : ι → A → ℝ, (∀ i a, |h i a| ≤ 1) → siteTestMean p E g h ≤ C)
    (hsquare : ∀ i, siteRowSquareMass p E i ≤ q) :
    finiteExpectation (siteProductMass p) (siteColumnResponse E g) ≤
      C + (Fintype.card ι : ℝ) * Real.sqrt q := by
  let K := fun i j a b => E j i b a * g j b
  have hKd : ∀ i a, K i i a a = 0 := by intro i a; simp [K,hdiag]
  have hKsq : ∀ i, siteRowSquareMass p K i ≤ q := by
    intro i
    refine (siteRowSquareMass_mono p hp K E ?_ i).trans (hsquare i)
    intro k j a b
    have hb : |K k j a b| ≤ |E k j a b| := by
      simp only [K,abs_mul]
      calc
        _ ≤ |E j k b a| * 1 := mul_le_mul_of_nonneg_left (hg j b) (abs_nonneg _)
        _ = _ := by rw [mul_one,hsym j k b a]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hb
  have hKt : ∀ h : ι → A → ℝ, (∀ i a, |h i a| ≤ 1) →
      finiteExpectation (siteProductMass p)
        (fun x => ∑ k, siteRowSum K k x*h k (x k)) ≤ C := by
    intro h hh
    convert htest h hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    simp only [siteRowSum,K,sum_mul]
    rw [sum_comm]
  have hb := siteRow_total_abs_of_tests p hp hpone K hKd C hKt
  change finiteExpectation (siteProductMass p) (siteColumnResponse E g) ≤ _ at hb
  refine hb.trans (add_le_add le_rfl ?_)
  calc
    _ ≤ ∑ _i : ι, Real.sqrt q := sum_le_sum fun i _ => Real.sqrt_le_sqrt (hKsq i)
    _ = _ := by simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConditionedRootTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring bounded tests to independent auxiliary roots -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

theorem finiteExpectation_abs_bound {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) :
    |finiteExpectation w f| ≤ finiteExpectation w (fun x => |f x|) := by
  unfold finiteExpectation
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro x _
  rw [abs_mul,abs_of_nonneg (hw x)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An averaged sharp cutoff for the coarse channel -/

namespace JointDickman

open MeasureTheory
open scoped NNReal

theorem averagingRamp_bounds {a b : ℝ} (hab : a < b) (x : ℝ) :
    0 ≤ averagingRamp a b x ∧ averagingRamp a b x ≤ 1 := by
  have hlo : a ≤ min b (max a x) := le_min hab.le (le_max_left _ _)
  have hhi : min b (max a x) ≤ b := min_le_left _ _
  unfold averagingRamp
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hab).le
  · apply (div_le_one (sub_pos.mpr hab)).mpr
    linarith

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockSiteErrorScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The block-site comparison error at the manuscript's cutoff scale -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_block_size_le_square (A : ℕ) :
    ∀ᶠ B : ℕ in atTop, A*amplificationMultiplier B ≤ B^2 := by
  filter_upwards [amplificationMultiplier_comparable,eventually_ge_atTop A,
    eventually_ge_atTop 1] with B hT hA hB
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : (B : ℝ)^(8/25 : ℝ) ≤ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hBreal (show (8/25 : ℝ) ≤ 1 by norm_num)
  have hTB : amplificationMultiplier B ≤ B := by exact_mod_cast hT.2.2.trans hpow
  calc
    _ ≤ B*B := Nat.mul_le_mul hA hTB
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ForwardLagSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the distinct forward lags of one block position -/

namespace JointDickman
open Finset

open Classical in
theorem forward_lag_singular_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i < k ∧ k.val-i.val < T then singularFactor 24 (k.val-i.val) else 0) ≤
      Real.exp 24*(T : ℝ) := by
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
    _ = ∑ k ∈ I, singularFactor 24 (k.val-i.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => k.val-i.val), singularFactor 24 j := (sum_image hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, singularFactor 24 j := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => zero_le_one.trans (singularFactor_one_le (by norm_num) j))
    _ ≤ _ := by
      simpa only [pow_one,Nat.cast_one,Nat.sub_self,pow_zero,one_mul,mul_one] using
        singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 T

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateKernelMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic polynomial bounds for both candidate kernels -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

theorem candidateMatrix_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (hv : ∀ e, 0 ≤ v e) (i k : κ) :
    0 ≤ candidateMatrix row col v i k := by
  apply sum_nonneg
  intro e _
  apply add_nonneg <;> split_ifs <;> first | exact hv e | exact le_rfl

theorem candidateMeanWeight_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (e : BlockCandidateIndex M) :
    0 ≤ candidateMeanWeight B L τ C S χ e := by
  exact finiteExpectation_nonneg _ _ (independentPrimeSetMass_nonneg B)
    (fun R => candidateRootWeight_nonneg B L τ C S χ hχ e R.val)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateSiteKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The latent graph as a kernel of its two endpoint types -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentCandidateKernel_symm (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) :
    latentCandidateKernel B L T H M τ C S χ i k =
      latentCandidateKernel B L T H M τ C S χ k i := by
  unfold latentCandidateKernel candidateMatrix
  apply sum_congr rfl
  intro e _
  dsimp only
  split_ifs <;> simp_all

theorem latentCandidateKernel_diag (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i : Fin M) :
    latentCandidateKernel B L T H M τ C S χ i i = 0 := by
  unfold latentCandidateKernel candidateMatrix
  apply sum_eq_zero
  intro e _
  have hord := (mem_blockCandidates.mp e.property).2.1
  dsimp only
  by_cases hi : i = e.val.1.1 <;> by_cases hk : i = e.val.1.2
  · have hh : e.val.1.1 = e.val.1.2 := hi.symm.trans hk
    rw [hh] at hord
    exact False.elim (lt_irrefl _ hord)
  all_goals simp [hi,hk,ne_of_lt hord,Ne.symm (ne_of_lt hord)]

theorem latentCandidateKernel_nonneg (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (i k : Fin M) :
    0 ≤ latentCandidateKernel B L T H M τ C S χ i k := by
  unfold latentCandidateKernel
  apply candidateMatrix_nonneg
  intro e
  exact candidateMeanWeight_nonneg B L τ C S χ hχ e.val

/-- Other endpoint types have no effect on this entry, even though the
full candidate list depends on the entire configuration. -/
theorem latentCandidateKernel_local {B L T H M : ℕ} {τ C : ℝ}
    (S R : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (i k : Fin M) (hi : S i = R i) (hk : S k = R k) :
    latentCandidateKernel B L T H M τ C S χ i k =
      latentCandidateKernel B L T H M τ C R χ i k := by
  have hf (i k : Fin M) (hik : i < k) (hi : S i = R i) (hk : S k = R k) :
      latentCandidateKernel B L T H M τ C S χ i k =
        latentCandidateKernel B L T H M τ C R χ i k := by
    rw [latentCandidateKernel_pair B L T H τ C S χ i k hik,
      latentCandidateKernel_pair B L T H τ C R χ i k hik]
    simp_rw [candidateMeanWeight_eq]
    rw [hi,hk]
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hf i k hik hi hk
  · rw [latentCandidateKernel_diag,latentCandidateKernel_diag]
  · rw [latentCandidateKernel_symm B L T H M τ C S χ,
      latentCandidateKernel_symm B L T H M τ C R χ]
    exact hf k i hki hk hi

theorem candidateSiteKernel_diag (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i : Fin M) (a b : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i i a b = 0 :=
  latentCandidateKernel_diag _ _ _ _ _ _ _ _ _ _

theorem candidateSiteKernel_nonneg (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (hχ : ∀ e, 0 ≤ χ e)
    (i k : Fin M) (a b : Finset ℕ) :
    0 ≤ candidateSiteKernel B L T H M τ C χ i k a b :=
  latentCandidateKernel_nonneg _ _ _ _ _ _ _ _ _ hχ _ _

theorem candidateSiteKernel_symm (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (a b : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i k a b =
      candidateSiteKernel B L T H M τ C χ k i b a := by
  by_cases h : i = k
  · subst k
    rw [candidateSiteKernel_diag,candidateSiteKernel_diag]
  · unfold candidateSiteKernel
    rw [latentCandidateKernel_symm]
    apply latentCandidateKernel_local <;> simp [h,Ne.symm h]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingRamp
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A continuous approximation of the actual counting-scale cutoff -/

namespace JointDickman
open Finset

theorem countingRamp_bounds {δ : ℝ} (hδ : 0 < δ) (s x : ℝ) :
    0 ≤ countingRamp δ s x ∧ countingRamp δ s x ≤ 1 :=
  averagingRamp_bounds (by linarith) x

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampedCandidate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual candidate cutoff and its ramped arithmetic counterpart -/
namespace JointDickman
open Finset

open Classical in
theorem rampedCandidateCutoff_bounds {M : ℕ} {δ : ℝ} (hδ : 0 < δ) (B T : ℕ)
    (σ : ℝ) (e : BlockCandidateIndex M) :
    0 ≤ rampedCandidateCutoff B T δ σ e ∧ rampedCandidateCutoff B T δ σ e ≤ 1 := by
  have hb : 0 ≤ candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e ∧
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e ≤ 1 := by
    unfold candidateCutoff amplificationOuterWeight amplificationInnerWeight
    have h1 := amplificationBump_bounds (Real.log (candidateQuotient e)/(B : ℝ))
    have h2 := amplificationBump_bounds ((candidateHigh e : ℝ)/(T*candidateQuotient e))
    have h3 := amplificationBump_bounds ((candidateLow e : ℝ)/(T*candidateQuotient e))
    constructor
    · exact mul_nonneg (mul_nonneg h1.1 h2.1) h3.1
    · exact (mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 zero_le_one) h3.2 h3.1
        (by norm_num)).trans_eq (by norm_num)
  have hr := countingRamp_bounds hδ σ ((candidateLow e : ℝ)/(T*candidateQuotient e))
  exact ⟨mul_nonneg hb.1 hr.1,
    (mul_le_mul hb.2 hr.2 hr.1 zero_le_one).trans_eq (one_mul _)⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SiteResponseConcentration
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential concentration of each fixed column response -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype A] [DecidableEq A]

theorem siteColumnResponse_concentration (hMC : FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEsym : ∀ i j a b, E i j a b = E j i b a)
    (hHsym : ∀ i j a b, H i j a b = H j i b a)
    (hEdiag : ∀ i a, E i i a a = 0) (hHdiag : ∀ i a, H i i a a = 0)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    (g : ι → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1)
    {C q d Ctest L u a : ℝ} (hd : 0 < d) (hgap : C < d)
    (hL : 0 ≤ L) (ha : 0 < a)
    (hmean : ∀ i b, |siteRowMean p H i b| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q)
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q)
    (htest : ∀ h : ι → A → ℝ, (∀ i b, |h i b| ≤ 1) → siteTestMean p E g h ≤ Ctest)
    (hbad : (Fintype.card ι : ℝ)*q/(d-C)^2 < 1)
    (hbound : Ctest/Fintype.card ι + Real.sqrt q +
      L*((Fintype.card ι : ℝ)*q/(d-C)^2) ≤ u)
    (hcut : u+a < L) :
    finiteProbability (siteProductMass p)
      (fun x => (∀ i, siteRowSum H i x ≤ d) ∧
        u+a < siteColumnResponse E g x/Fintype.card ι) ≤
      Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let G : Finset (ι → A) := univ.filter (fun x => ∀ i, siteRowSum H i x ≤ d)
  have hGmem (x : ι → A) : x ∈ G ↔ ∀ i, siteRowSum H i x ≤ d := by simp [G]
  have hprob := siteDegree_bad_probability p hp hpone H hHdiag hgap hmean hsquareH
  have hG : G.Nonempty := by
    by_contra hne
    have hb (x : ι → A) : ¬ ∀ i, siteRowSum H i x ≤ d := by
      intro hx
      exact hne ⟨x,(hGmem x).mpr hx⟩
    have he : finiteProbability (siteProductMass p)
        (fun x => ¬ ∀ i, siteRowSum H i x ≤ d) = 1 := by
      simp only [finiteProbability,hb]
      exact siteProductMass_sum p hpone
    rw [he] at hprob
    linarith
  have hresp := siteColumnResponse_mean_le p hp hpone E hEsym hEdiag g hg Ctest q htest hsquareE
  have hmeanZ : finiteExpectation (siteProductMass p)
      (fun x => siteColumnResponse E g x/Fintype.card ι) +
      L*finiteProbability (siteProductMass p) (fun x => x ∉ G) ≤ u := by
    rw [finiteExpectation_div]
    have hpg : finiteProbability (siteProductMass p) (fun x => x ∉ G) ≤
        (Fintype.card ι : ℝ)*q/(d-C)^2 := by
      simpa only [hGmem] using hprob
    have hr := div_le_div_of_nonneg_right hresp hN.le
    rw [add_div,mul_div_cancel_left₀ _ hN.ne'] at hr
    exact (add_le_add hr (mul_le_mul_of_nonneg_left hpg hL)).trans hbound
  have hlip : ∀ x ∈ G, ∀ y ∈ G,
      |siteColumnResponse E g x/Fintype.card ι - siteColumnResponse E g y/Fintype.card ι| ≤
        (4*d/Fintype.card ι)*hammingDist x y := by
    intro x hx y hy
    rw [← sub_div,abs_div,abs_of_pos hN]
    have hh := div_le_div_of_nonneg_right
      (siteColumnResponse_lipschitz_on_good E H g hHsym hdom hg d x y
        ((hGmem x).mp hx) ((hGmem y).mp hy)) hN.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hh := goodSet_concentration hMC p hp hpone G hG
    (fun x => siteColumnResponse E g x/Fintype.card ι)
    (div_nonneg (by positivity) hN.le) hL ha
    (fun x => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) hN.le) hlip hmeanZ hcut
  have hexp : -2*a^2/((Fintype.card ι : ℝ)*(4*d/Fintype.card ι)^2) =
      -(a^2*(Fintype.card ι : ℝ))/(8*d^2) := by
    field_simp
    ring
  simpa only [hGmem,hexp] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SampledSiteResponse
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying a column sample after its site types are fixed -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

omit [Fintype ι] [Fintype A] [DecidableEq ι] in
theorem sampledSiteTest_bound (E : ι → ι → A → A → ℝ) {m : ℕ}
    (s : ColumnSample (ι := ι) m) (t : ι → A) (i : ι) (a : A) :
    |sampledSiteTest E s t i a| ≤ 1 := by simp [sampledSiteTest]

omit [Fintype ι] [Fintype A] in
theorem sampledSiteTest_agree (E : ι → ι → A → A → ℝ) {m : ℕ}
    (s : ColumnSample (ι := ι) m) (t x : ι → A)
    (ht : ∀ i ∈ univ.image s.1, x i = t i) :
    sampledSiteTest E s t = sampledSiteTest E s x := by
  funext i a
  unfold sampledSiteTest
  congr 1
  apply sum_congr rfl
  intro r _
  rw [ht (s.1 r) (mem_image.mpr ⟨r,mem_univ _,rfl⟩)]

omit [Fintype A] in
theorem siteColumnResponse_masked (E : ι → ι → A → A → ℝ)
    (g : ι → A → ℝ) (J : Finset ι) (x : ι → A) :
    siteColumnResponse (maskedSiteKernel J E) g x =
      residualColumnBound (realizedSiteKernel E x) J (fun i => g i (x i)) := by
  have he : univ \ J = univ.filter (fun i => i ∉ J) := by ext i; simp
  simp only [siteColumnResponse,residualColumnBound,he,sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases hj : j ∈ J
  · simp [maskedSiteKernel,hj]
  · simp only [maskedSiteKernel,hj,not_false_eq_true,and_true,ite_mul,zero_mul,realizedSiteKernel]
    simp only [ite_true, if_true]

omit [Fintype A] in
theorem columnSampleNorm_eq_response (E : ι → ι → A → A → ℝ) {m : ℕ}
    (s : ColumnSample (ι := ι) m) (x : ι → A) :
    columnSampleNorm (realizedSiteKernel E x) s =
      siteColumnResponse (maskedSiteKernel (univ.image s.1) E) (sampledSiteTest E s x) x /
        Fintype.card ι := by
  rw [siteColumnResponse_masked]
  rfl

omit [Fintype A] in
theorem maskedSiteKernel_row_le (H : ι → ι → A → A → ℝ)
    (hH : ∀ i j a b, 0 ≤ H i j a b) (J : Finset ι) (x : ι → A) (i : ι) :
    siteRowSum (maskedSiteKernel J H) i x ≤ siteRowSum H i x := by
  apply sum_le_sum
  intro j _
  unfold maskedSiteKernel
  split_ifs <;> first | exact le_rfl | exact hH i j (x i) (x j)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SampledColumnTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform tails for the finite family of column samples -/

namespace JointDickman
open Finset Classical PublishedInputs

theorem finiteProbability_eq_expectation {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (P : Ω → Prop) :
    finiteProbability w P = finiteExpectation w (fun x => if P x then 1 else 0) := by
  unfold finiteProbability finiteExpectation
  apply sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype A] [DecidableEq A]

theorem sampledColumn_tail (hMC : FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEsym : ∀ i j a b, E i j a b = E j i b a)
    (hHsym : ∀ i j a b, H i j a b = H j i b a)
    (hEdiag : ∀ i a, E i i a a = 0) (hHdiag : ∀ i a, H i i a a = 0)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    {C q d e L u a : ℝ} (hC : 0 ≤ C) (hd : 0 < d) (hgap : C < d)
    (hL : 0 ≤ L) (ha : 0 < a)
    (hmean : ∀ i b, |siteRowMean p H i b| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q)
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q)
    (htest : ∀ g h : ι → A → ℝ, (∀ i b, |g i b| ≤ 1) → (∀ i b, |h i b| ≤ 1) →
      siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e)
    (hbad : (Fintype.card ι : ℝ)*q/(d-C)^2 < 1)
    (hbound : e + Real.sqrt q + L*((Fintype.card ι : ℝ)*q/(d-C)^2) ≤ u)
    (hcut : u+a < L) {m : ℕ} (s : ColumnSample (ι := ι) m) :
    finiteProbability (siteProductMass p)
      (fun x => (∀ i, siteRowSum H i x ≤ d) ∧
        u+a < columnSampleNorm (realizedSiteKernel E x) s) ≤
      Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)) := by
  let J : Finset ι := univ.image s.1
  let R := maskedSiteKernel J E
  let V := maskedSiteKernel J H
  let Z := fun t x => siteColumnResponse R (sampledSiteTest E s t) x/Fintype.card ι
  have hH : ∀ i j b c, 0 ≤ H i j b c := fun i j b c => (abs_nonneg _).trans (hdom i j b c)
  have hR : ∀ i j b c, R i j b c = R j i c b := by
    intro i j b c
    simp only [R,maskedSiteKernel]
    simp only [and_comm]
    rw [hEsym]
  have hV : ∀ i j b c, V i j b c = V j i c b := by
    intro i j b c
    simp only [V,maskedSiteKernel]
    simp only [and_comm]
    rw [hHsym]
  have hRV : ∀ i j b c, |R i j b c| ≤ V i j b c := by
    intro i j b c
    dsimp only [R,V,maskedSiteKernel]
    split_ifs <;> first | exact hdom i j b c | simp
  have htail (t : ι → A) :
      finiteProbability (siteProductMass (frozenSiteMass p J t))
        (fun x => (∀ i, siteRowSum H i x ≤ d) ∧ u+a < Z t x) ≤
        Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)) := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hh := siteColumnResponse_concentration hMC (frozenSiteMass p J t)
      (frozenSiteMass_nonneg p hp J t) (frozenSiteMass_sum p hpone J t) R V hR hV
      (maskedSiteKernel_diag J E hEdiag) (maskedSiteKernel_diag J H hHdiag) hRV
      (sampledSiteTest E s t) (sampledSiteTest_bound E s t) hd hgap hL ha
      (maskedSiteKernel_mean_le p hp J t H hH hC hmean)
      (fun i => (maskedSiteKernel_square_le p hp J t H i).trans (hsquareH i))
      (fun i => (maskedSiteKernel_square_le p hp J t E i).trans (hsquareE i))
      (fun h hh => siteTestMean_restriction_bound p hpone E _ htest J t _ h
        (sampledSiteTest_bound E s t) hh) hbad
      (by simpa only [mul_div_cancel_left₀ _ hn] using hbound) hcut
    refine (finiteProbability_mono _
      (siteProductMass_nonneg _ (frozenSiteMass_nonneg p hp J t)) ?_).trans hh
    intro x hx
    exact ⟨fun i => (maskedSiteKernel_row_le H hH J x i).trans (hx.1 i),hx.2⟩
  let F : (ι → A) → (ι → A) → ℝ := fun t x =>
    if (∀ i, siteRowSum H i x ≤ d) ∧ u+a < Z t x then 1 else 0
  have hF : ∀ t x, (∀ i ∈ J, x i = t i) → F t x = F x x := by
    intro t x hx
    have he := sampledSiteTest_agree E s t x hx
    simp only [F,Z,he]
  have hid := frozenSiteMass_disintegrate p hpone J F hF
  rw [finiteProbability_eq_expectation]
  have hz (x : ι → A) : columnSampleNorm (realizedSiteKernel E x) s = Z x x :=
    columnSampleNorm_eq_response E s x
  simp only [hz]
  change finiteExpectation (siteProductMass p) (fun x => F x x) ≤ _
  rw [hid]
  calc
    _ ≤ finiteExpectation (siteProductMass p)
        (fun _ => Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2))) := by
      apply finiteExpectation_mono _ (siteProductMass_nonneg p hp)
      intro t
      have hh := htail t
      rw [finiteProbability_eq_expectation] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      unfold finiteExpectation
      apply sum_congr rfl
      intro x _
      by_cases hx : (∀ i, siteRowSum H i x ≤ d) ∧ u+a < Z t x <;> simp [F,hx]
    _ = _ := finiteExpectation_const _ (siteProductMass_sum p hpone) _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCandidateModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite prime-feature model for each ramped candidate entry -/
namespace JointDickman
open Finset

theorem countingCandidateModel_bound (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L j : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (H : (Fin 4 →₀ ℕ) → ℕ) (T σ K : ℝ)
    (hseries : 0 ≤ singularSeries j)
    (hK : ∀ x y, |countingPrimeKernel P m B j c H T σ x y| ≤ K)
    (S R : Finset ℕ) :
    |countingCandidateModel P m B L j τ C c H T σ S R| ≤
      (independentRootMean B L τ C*(singularSeries j/(j : ℝ)))*K := by
  unfold countingCandidateModel subsetPrimeModel
  rw [abs_mul,abs_of_nonneg (mul_nonneg (independentRootMean_nonneg ..)
    (div_nonneg hseries (Nat.cast_nonneg _)))]
  exact mul_le_mul_of_nonneg_left (hK _ _) (mul_nonneg (independentRootMean_nonneg ..)
    (div_nonneg hseries (Nat.cast_nonneg _)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateSiteMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform means in either orientation of the latent site kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem backward_lag_singular_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if k < i ∧ i.val-k.val < T then singularFactor 24 (i.val-k.val) else 0) ≤
      Real.exp 24*(T : ℝ) := by
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
    _ = ∑ k ∈ I, singularFactor 24 (i.val-k.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => i.val-k.val), singularFactor 24 j := (sum_image hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, singularFactor 24 j := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => zero_le_one.trans (singularFactor_one_le (by norm_num) j))
    _ ≤ _ := by
      simpa only [pow_one,Nat.cast_one,Nat.sub_self,pow_zero,one_mul,mul_one] using
        singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 T

theorem distance_lag_singular_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
      singularFactor 24 (Nat.dist i.val k.val) else 0) ≤ 2*Real.exp 24*(T : ℝ) := by
  have he (k : Fin M) :
      (if i ≠ k ∧ Nat.dist i.val k.val < T then singularFactor 24 (Nat.dist i.val k.val) else 0) =
      (if i < k ∧ k.val-i.val < T then singularFactor 24 (k.val-i.val) else 0) +
      (if k < i ∧ i.val-k.val < T then singularFactor 24 (i.val-k.val) else 0) := by
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le,Nat.dist_eq_sub_of_le h.le]
    · simp
    · simp [h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le,Nat.dist_eq_sub_of_le_right h.le]
  simp_rw [he]
  rw [sum_add_distrib]
  have hf := forward_lag_singular_sum i T
  have hb := backward_lag_singular_sum i T
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LagSquareSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-moment lag sum for the finite-feature envelope -/
namespace JointDickman
open Finset Classical

private theorem forward_lag_square_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i < k ∧ k.val-i.val < T then (singularFactor 24 (k.val-i.val))^2 else 0) ≤
      Real.exp 1200*(T : ℝ) := by
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
    _ = ∑ k ∈ I, (singularFactor 24 (k.val-i.val))^2 := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => k.val-i.val), (singularFactor 24 j)^2 := (sum_image (f := fun j : ℕ => (singularFactor 24 j)^2) hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, (singularFactor 24 j)^2 := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => sq_nonneg _)
    _ ≤ _ := by
      convert singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 2 T using 1
      all_goals try with_reducible_and_instances rfl
      norm_num

private theorem backward_lag_square_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if k < i ∧ i.val-k.val < T then (singularFactor 24 (i.val-k.val))^2 else 0) ≤
      Real.exp 1200*(T : ℝ) := by
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
    _ = ∑ k ∈ I, (singularFactor 24 (i.val-k.val))^2 := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => i.val-k.val), (singularFactor 24 j)^2 := (sum_image (f := fun j : ℕ => (singularFactor 24 j)^2) hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, (singularFactor 24 j)^2 := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => sq_nonneg _)
    _ ≤ _ := by
      convert singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 2 T using 1
      all_goals try with_reducible_and_instances rfl
      norm_num

theorem distance_lag_square_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
      (singularFactor 24 (Nat.dist i.val k.val))^2 else 0) ≤ 2*Real.exp 1200*(T : ℝ) := by
  have he (k : Fin M) :
      (if i ≠ k ∧ Nat.dist i.val k.val < T then (singularFactor 24 (Nat.dist i.val k.val))^2 else 0) =
      (if i < k ∧ k.val-i.val < T then (singularFactor 24 (k.val-i.val))^2 else 0) +
      (if k < i ∧ i.val-k.val < T then (singularFactor 24 (i.val-k.val))^2 else 0) := by
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le,Nat.dist_eq_sub_of_le h.le]
    · simp
    · simp [h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le,Nat.dist_eq_sub_of_le_right h.le]
  simp_rw [he]
  rw [sum_add_distrib]
  have hf := forward_lag_square_sum i T
  have hb := backward_lag_square_sum i T
  linarith

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

theorem singularSeries_le_singularFactor
    (hMP : PublishedInputs.PrimeProductMertensInput) {j : ℕ} (hj : 0 < j) :
    singularSeries j ≤ singularFactor 24 j :=
  (singularSeries_bounds hMP j).2.trans (totient_ratio_le_singularFactor hj)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSiteModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The symmetric finite-feature block model and its lag envelope -/
namespace JointDickman
open Finset Classical

theorem countingSiteModel_diag (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    countingSiteModel P m B L T H M τ C c D σ i i a b = 0 := by
  simp only [countingSiteModel,lt_self_iff_false,ite_false, if_false]

theorem countingSiteModel_symm (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    countingSiteModel P m B L T H M τ C c D σ i k a b =
      countingSiteModel P m B L T H M τ C c D σ k i b a := by
  rcases lt_trichotomy i k with h | rfl | h
  · simp only [countingSiteModel,h,not_lt_of_ge h.le,ite_true, if_true,ite_false, if_false]
  · rw [countingSiteModel_diag,countingSiteModel_diag]
  · simp only [countingSiteModel,h,not_lt_of_ge h.le,ite_true, if_true,ite_false, if_false]

theorem countingCandidateModel_lag_bound
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {T η C₀ σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hlag : η*T ≤ j)
    (hbound : ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (a b : Finset ℕ) :
    |countingCandidateModel P m B L j τ C c D T σ a b| ≤
      (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 j := by
  have hjr : (0 : ℝ) < j := (mul_pos hη hT).trans_le hlag
  have hj : 0 < j := by exact_mod_cast hjr
  have hsf : 0 ≤ singularFactor 24 j := zero_le_one.trans (singularFactor_one_le (by norm_num) j)
  have he : singularSeries j/(j : ℝ) ≤ singularFactor 24 j/(η*T) :=
    (div_le_div_of_nonneg_right (singularSeries_le_singularFactor hMP hj) hjr.le).trans
      (div_le_div_of_nonneg_left hsf (mul_pos hη hT) hlag)
  calc
    _ ≤ (independentRootMean B L τ C*(singularSeries j/(j : ℝ)))*C₀ :=
      countingCandidateModel_bound P m B L j τ C c D T σ C₀ (singularSeries_bounds hMP j).1 hbound a b
    _ ≤ (independentRootMean B L τ C*(singularFactor 24 j/(η*T)))*C₀ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (independentRootMean_nonneg ..)) hC₀
    _ = _ := by ring

theorem countingSiteModel_lag_envelope
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {η C₀ σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      if i ≠ k ∧ Nat.dist i.val k.val < T then
        (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) else 0 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hf (i k : Fin M) (hik : i < k) (a b : (auxiliaryPrimes B).powerset) :
      |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      if i ≠ k ∧ Nat.dist i.val k.val < T then
        (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) else 0 := by
    rw [countingSiteModel,ite_eq_left hik,Nat.dist_eq_sub_of_le hik.le]
    by_cases ha : H < k.val-i.val ∧ k.val-i.val < T
    · rw [ite_eq_left ha,ite_eq_left ⟨ne_of_lt hik,ha.2⟩]
      apply countingCandidateModel_lag_bound hMP P m B L _ τ C c D hTr hη hC₀ _ (hbound _ ha.1 ha.2)
      exact hH.trans (by exact_mod_cast ha.1.le)
    · rw [ite_eq_right ha,abs_zero]
      split_ifs
      · exact mul_nonneg (div_nonneg (mul_nonneg (independentRootMean_nonneg ..) hC₀)
          (mul_pos hη hTr).le) (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
      · exact le_rfl
  rcases lt_trichotomy i k with h | rfl | h
  · exact hf i k h a b
  · simp only [countingSiteModel_diag,ne_eq,not_true_eq_false,false_and,ite_false, if_false,abs_zero,le_refl]
  · rw [countingSiteModel_symm, Nat.dist_comm i.val k.val]
    have hh := hf k i h b a
    simpa only [ne_comm] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LagEnvelopeMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Row moments of the deterministic singular-factor envelope -/
namespace JointDickman
open Finset Classical PublishedInputs

theorem lagEnvelope_nonneg {M : ℕ} (T : ℕ) {D : ℝ} (hD : 0 ≤ D) (i k : Fin M) :
    0 ≤ lagEnvelope T D i k := by
  unfold lagEnvelope
  split_ifs
  · exact mul_nonneg (div_nonneg hD (Nat.cast_nonneg _))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
  · exact le_rfl

theorem lagEnvelope_row_sum {M T : ℕ} (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D) (i : Fin M) :
    (∑ k, lagEnvelope T D i k) ≤ 2*D*Real.exp 24 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have he (k : Fin M) : lagEnvelope T D i k = D/(T : ℝ)*
      (if i ≠ k ∧ Nat.dist i.val k.val < T then singularFactor 24 (Nat.dist i.val k.val) else 0) := by
    unfold lagEnvelope
    split_ifs <;> simp only [mul_zero]
  simp_rw [he]
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (distance_lag_singular_sum i T) (div_nonneg hD hTr.le)).trans_eq
    (by field_simp)

theorem lagEnvelope_row_square_sum {M T : ℕ} (hT : 0 < T) {D : ℝ} (i : Fin M) :
    (∑ k, (lagEnvelope T D i k)^2) ≤ 2*D^2*Real.exp 1200/(T : ℝ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have he (k : Fin M) : (lagEnvelope T D i k)^2 = (D/(T : ℝ))^2*
      (if i ≠ k ∧ Nat.dist i.val k.val < T then (singularFactor 24 (Nat.dist i.val k.val))^2 else 0) := by
    unfold lagEnvelope
    split_ifs <;> simp only [mul_pow,mul_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp_rw [he]
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (distance_lag_square_sum i T) (sq_nonneg _)).trans_eq
    (by field_simp)

theorem lagEnvelope_row_mean {M T : ℕ} {A : Type*} [Fintype A]
    (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D) (p : Fin M → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : Fin M → Fin M → A → A → ℝ)
    (hK : ∀ i k a b, |K i k a b| ≤ lagEnvelope T D i k) (i : Fin M) (a : A) :
    |siteRowMean p K i a| ≤ 2*D*Real.exp 24 := by
  have he (k : Fin M) :
      |finiteExpectation (p k) (fun b => K i k a b)| ≤ lagEnvelope T D i k :=
    (finiteExpectation_abs_bound (p k) _ (hp k)).trans
      ((finiteExpectation_mono (p k) (hp k) (hK i k a)).trans_eq
        (finiteExpectation_const (p k) (hpone k) _))
  calc
    _ ≤ ∑ k : {k : Fin M // k ≠ i}, |finiteExpectation (p k) (fun b => K i k a b)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : {k : Fin M // k ≠ i}, lagEnvelope T D i k := sum_le_sum (fun k _ => he k)
    _ = ∑ k : Fin M, lagEnvelope T D i k := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
      simp only [lagEnvelope,ne_eq,not_true_eq_false,false_and,ite_false, if_false,zero_add]
    _ ≤ _ := lagEnvelope_row_sum hT hD i

theorem lagEnvelope_row_square_mass {M T : ℕ} {A : Type*} [Fintype A]
    (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D) (p : Fin M → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : Fin M → Fin M → A → A → ℝ)
    (hK : ∀ i k a b, |K i k a b| ≤ lagEnvelope T D i k) (i : Fin M) :
    siteRowSquareMass p K i ≤ 2*D^2*Real.exp 1200/(T : ℝ) := by
  have he (k : Fin M) (a : A) :
      finiteExpectation (p k) (fun b => (K i k a b)^2) ≤ (lagEnvelope T D i k)^2 := by
    apply (finiteExpectation_mono (p k) (hp k) (fun b => ?_)).trans_eq
      (finiteExpectation_const (p k) (hpone k) _)
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (lagEnvelope_nonneg T hD i k)).mpr (hK i k a b)
  have hr (a : A) : (∑ k : {k : Fin M // k ≠ i},
      finiteExpectation (p k) (fun b => (K i k a b)^2)) ≤ 2*D^2*Real.exp 1200/(T : ℝ) := by
    calc
      _ ≤ ∑ k : {k : Fin M // k ≠ i}, (lagEnvelope T D i k)^2 := sum_le_sum (fun k _ => he k a)
      _ = ∑ k : Fin M, (lagEnvelope T D i k)^2 := by
        rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
        simp only [lagEnvelope,ne_eq,not_true_eq_false,false_and,ite_false, if_false,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add]
      _ ≤ _ := lagEnvelope_row_square_sum hT i
  exact (finiteExpectation_mono (p i) (hp i) hr).trans_eq
    (finiteExpectation_const (p i) (hpone i) _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingModelEnvelope
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform lag envelope at the actual amplification scale -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem countingSiteModel_uniform_envelope
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {η C₀ R σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀)
    (hroot : independentRootMean B L τ C ≤ R) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      lagEnvelope T (R*C₀/η) i k := by
  apply (countingSiteModel_lag_envelope hMP P m B L T H M τ C c D
    hT hη hC₀ hH hbound i k a b).trans
  unfold lagEnvelope
  split_ifs
  · have hden : 0 ≤ η*(T : ℝ) := mul_nonneg hη.le (Nat.cast_nonneg _)
    have hs : 0 ≤ singularFactor 24 (Nat.dist i.val k.val) :=
      zero_le_one.trans (singularFactor_one_le (by norm_num) _)
    calc
      _ ≤ (R*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hC₀) hden) hs
      _ = _ := by ring
  · exact le_rfl

theorem amplification_sampling_scale : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
    (amplificationMultiplier B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) ∧
    amplificationMultiplier B ≤ auxiliaryCutoff B ∧
    (amplificationMultiplier B : ℝ) ≤ (B : ℝ)^2 ∧
    Real.log (amplificationMultiplier B) ≤ (B : ℝ)/10 ∧
    (B : ℝ)^(32/100 : ℝ)/2 ≤ amplificationMultiplier B := by
  filter_upwards [amplificationMultiplier_valid,amplificationMultiplier_comparable,
    amplification_block_size_le_square 1,eventually_ge_atTop 1] with B hv hc hs hB
  have hs' : amplificationMultiplier B ≤ B^2 := by simpa using hs
  have hcut : B^2 ≤ auxiliaryCutoff B :=
    pow_le_pow_right₀ hB (by norm_num : 2 ≤ 1000)
  refine ⟨hv.1,hv.2,hs'.trans hcut,by exact_mod_cast hs',?_,?_⟩
  · have hlog := Real.log_le_log (by exact_mod_cast hv.1) hv.2
    rw [Real.log_exp] at hlog
    convert hlog using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · convert hc.2.1 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FiniteSamplingComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative comparison with the fully adaptive cut

The finite family tail is proved from McDiarmid's published input. All
remaining hypotheses here are the displayed first- and second-moment and
single-site-test inequalities used by the manuscript's application.
-/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype A] [DecidableEq A]

theorem finiteSamplingComparison (hMC : FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEsym : ∀ i j a b, E i j a b = E j i b a)
    (hHsym : ∀ i j a b, H i j a b = H j i b a)
    (hEdiag : ∀ i a, E i i a a = 0) (hHdiag : ∀ i a, H i i a a = 0)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    {C q d Q e L u a : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hd : 0 < d) (hQ : 0 < Q) (hgap : C < d) (hu : 0 ≤ u)
    (hL : 0 ≤ L) (ha : 0 < a)
    (hmean : ∀ i b, |siteRowMean p H i b| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q)
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q)
    (htest : ∀ g h : ι → A → ℝ, (∀ i b, |g i b| ≤ 1) → (∀ i b, |h i b| ≤ 1) →
      siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e)
    (hbad : (Fintype.card ι : ℝ)*q/(d-C)^2 < 1)
    (hbound : e + Real.sqrt q + L*((Fintype.card ι : ℝ)*q/(d-C)^2) ≤ u)
    (hcut : u+a < L) (m : ℕ) (hm : 0 < m) :
    finiteExpectation (siteProductMass p)
      (fun x => kernelCutNorm (realizedSiteKernel E x)) ≤
      u+a + samplingError (ι := ι) d Q m +
        Real.sqrt ((C^2+q)*((Fintype.card ι : ℝ)*q/(d-C)^2+
          (Fintype.card ι : ℝ)*q/Q +
          (((2*Fintype.card ι)^m : ℕ) : ℝ)*
            Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)))) := by
  let G := SiteKernelGood E H d Q
  have htail (s : ColumnSample (ι := ι) m) :
      finiteProbability (siteProductMass p)
        (fun x => G x ∧ u+a < columnSampleNorm (realizedSiteKernel E x) s) ≤
        Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)) := by
    refine (finiteProbability_mono _ (siteProductMass_nonneg p hp) ?_).trans
      (sampledColumn_tail hMC p hp hpone E H hEsym hHsym hEdiag hHdiag hdom
        hC hd hgap hL ha hmean hsquareH hsquareE htest hbad hbound hcut s)
    intro x hx
    exact ⟨hx.1.1,hx.2⟩
  have hsquare : ∀ i, (∑ j, finiteExpectation (siteProductMass p)
      (fun x => H i j (x i) (x j)^2)) ≤ q := by
    intro i
    rw [← siteRowSquareMass_eq_sum_entries p hpone H hHdiag i]
    exact hsquareH i
  have hthreshold : 0 ≤ u+a+samplingError (ι := ι) d Q m := by
    apply add_nonneg (add_nonneg hu ha.le)
    unfold samplingError
    positivity
  have hb := siteKernel_sampling_transfer p hp hpone E H G hdom hHdiag hEsym
    C q d Q (u+a) (Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2))) m hm hq
    hmean hsquare hthreshold
    (fun x hx i => (sum_le_sum fun j _ => hdom i j (x i) (x j)).trans (hx.1 i))
    (fun _ hx => hx.2) htail
  refine hb.trans (add_le_add le_rfl (Real.sqrt_le_sqrt ?_))
  apply mul_le_mul_of_nonneg_left _ (add_nonneg (sq_nonneg C) hq)
  exact add_le_add (siteKernelGood_bad_probability p hp hpone E H hEdiag hHdiag
    hgap hQ hmean hsquareH hsquareE) le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingErrorBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar bounds for the manuscript's sampling scales -/

namespace JointDickman
open Filter
open scoped Topology

theorem samplingError_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    (d Q : ℝ) (m : ℕ) :
    samplingError (ι := ι) d Q m =
      2*Real.sqrt (Q/(m : ℝ))+2*m*d/Fintype.card ι := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card ι : ℝ)*((Fintype.card ι : ℝ)/m*Q) =
      (Fintype.card ι : ℝ)^2*(Q/m) := by ring
  unfold samplingError
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hN.le,add_div]
  field_simp

theorem samplingError_scale_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    {B c U K : ℝ} (hB : 1 ≤ B) (hc : 0 < c) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hNlo : c*B^(0.32 : ℝ) ≤ Fintype.card ι)
    (hNhi : (Fintype.card ι : ℝ) ≤ U*B^(0.32 : ℝ))
    (m : ℕ) (hmlo : B^(0.14 : ℝ) ≤ m) (hmhi : (m : ℝ) ≤ 2*B^(0.14 : ℝ)) :
    samplingError (ι := ι) (K*B^(0.07 : ℝ))
      ((Fintype.card ι : ℝ)*B^(-0.20 : ℝ)) m ≤
      2*Real.sqrt (U*(B^(0.12 : ℝ)/B^(0.14 : ℝ))) +
        (4*K/c)*(B^(0.21 : ℝ)/B^(0.32 : ℝ)) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hm : (0 : ℝ) < m := (Real.rpow_pos_of_pos hB0 _).trans_le hmlo
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [samplingError_eq]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ (U*B^(0.32 : ℝ)*B^(-0.20 : ℝ))/B^(0.14 : ℝ) := by
        gcongr
      _ = _ := by
        rw [mul_assoc,← Real.rpow_add hB0]
        norm_num
        ring
  · calc
      _ ≤ 2*(2*B^(0.14 : ℝ))*(K*B^(0.07 : ℝ))/(c*B^(0.32 : ℝ)) := by
        gcongr
      _ = _ := by
        have he : B^(0.14 : ℝ)*B^(0.07 : ℝ) = B^(0.21 : ℝ) := by
          rw [← Real.rpow_add hB0]
          norm_num
        field_simp
        nlinarith [he]

theorem sampling_degree_scale_bound {N B C q K U : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hq : 0 ≤ q) (hK : 0 < K) (hN : 0 ≤ N)
    (hNhi : N ≤ U*B^(0.32 : ℝ)) (hgap : 2*C ≤ K*B^(0.07 : ℝ)) :
    N*(q*B^(-0.21 : ℝ))/(K*B^(0.07 : ℝ)-C)^2 ≤
      (4*U*q/K^2)*(B^(0.11 : ℝ)/B^(0.14 : ℝ)) := by
  have hd : 0 < K*B^(0.07 : ℝ) := mul_pos hK (Real.rpow_pos_of_pos hB _)
  have hg : 0 < K*B^(0.07 : ℝ)-C := by linarith
  have hUn : 0 ≤ U*B^(0.32 : ℝ) := hN.trans hNhi
  have hs : (K*B^(0.07 : ℝ))^2/4 ≤ (K*B^(0.07 : ℝ)-C)^2 := by nlinarith
  calc
    _ ≤ (U*B^(0.32 : ℝ))*(q*B^(-0.21 : ℝ))/((K*B^(0.07 : ℝ))^2/4) := by
      gcongr
    _ = _ := by
      have he : B^(0.32 : ℝ)*B^(-0.21 : ℝ) = B^(0.11 : ℝ) := by
        rw [← Real.rpow_add hB]; norm_num
      have he2 : (B^(0.07 : ℝ))^2 = B^(0.14 : ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hB.le]; norm_num
      rw [mul_pow,he2]
      have hn : (U*B^(0.32 : ℝ))*(q*B^(-0.21 : ℝ)) = U*q*B^(0.11 : ℝ) := by
        calc
          _ = U*q*(B^(0.32 : ℝ)*B^(-0.21 : ℝ)) := by ring
          _ = _ := by rw [he]
      rw [hn]
      field_simp

theorem sampling_square_scale_eq {N B q : ℝ} (hN : N ≠ 0) (hB : 0 < B) :
    N*(q*B^(-0.21 : ℝ))/(N*B^(-0.20 : ℝ)) =
      q*(B^(0.20 : ℝ)/B^(0.21 : ℝ)) := by
  rw [Real.rpow_neg hB.le,Real.rpow_neg hB.le]
  field_simp

theorem sampling_error_envelope_tendsto (U K c : ℝ) :
    Tendsto (fun B : ℝ => 2*Real.sqrt (U*(B^(0.12 : ℝ)/B^(0.14 : ℝ)))+
      (4*K/c)*(B^(0.21 : ℝ)/B^(0.32 : ℝ))) atTop (𝓝 0) := by
  have h₁ := ((power_div_power_tendsto_zero (a := (0.12 : ℝ)) (b := (0.14 : ℝ))
    (by norm_num)).const_mul U).sqrt.const_mul 2
  have h₂ := (power_div_power_tendsto_zero (a := (0.21 : ℝ)) (b := (0.32 : ℝ))
    (by norm_num)).const_mul (4*K/c)
  simpa using h₁.add h₂

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingFamilyRate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The column-family entropy is absorbed by concentration -/

namespace JointDickman
open Filter
open scoped Topology

theorem samplingFamily_scale_bound {B c K a : ℝ} {N m : ℕ}
    (hB : 1 ≤ B) (hc : 0 < c) (hK : 0 < K) (hN : 0 < N)
    (hNlo : c*B^(0.32 : ℝ) ≤ N) (hNhi : (2 : ℝ)*N ≤ B)
    (hm : (m : ℝ) ≤ 2*B^(0.14 : ℝ)) :
    (((2*N)^m : ℕ) : ℝ)*Real.exp (-(a^2*(N : ℝ))/(8*(K*B^(0.07 : ℝ))^2)) ≤
      Real.exp (2*(B^(0.14 : ℝ)*Real.log B) -
        (a^2*c/(8*K^2))*B^(0.18 : ℝ)) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hn : (0 : ℝ) < 2*N := by exact_mod_cast (Nat.mul_pos (by omega) hN)
  have hlog : (m : ℝ)*Real.log (2*N) ≤ 2*(B^(0.14 : ℝ)*Real.log B) := by
    have hh := mul_le_mul hm (Real.log_le_log hn hNhi)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*N by omega)))
      (by positivity : 0 ≤ 2*B^(0.14 : ℝ))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hquot : (a^2*c/(8*K^2))*B^(0.18 : ℝ) ≤
      (a^2*(N : ℝ))/(8*(K*B^(0.07 : ℝ))^2) := by
    calc
      _ = (a^2*(c*B^(0.32 : ℝ)))/(8*(K*B^(0.07 : ℝ))^2) := by
        have he : (B^(0.07 : ℝ))^2*B^(0.18 : ℝ) = B^(0.32 : ℝ) := by
          rw [← Real.rpow_natCast,← Real.rpow_mul hB0.le,← Real.rpow_add hB0]
          norm_num
        field_simp
        nlinarith [he]
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNlo (sq_nonneg a)) (by positivity)
  have he : (((2*N)^m : ℕ) : ℝ) = Real.exp ((m : ℝ)*Real.log (2*N)) := by
    rw [Real.exp_nat_mul,Real.exp_log hn]
    push_cast
    rfl
  rw [he,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [sub_eq_add_neg,neg_div] using sub_le_sub hlog hquot

theorem samplingFamily_envelope_tendsto {c K a : ℝ}
    (hc : 0 < c) (hK : 0 < K) (ha : 0 < a) :
    Tendsto (fun B : ℝ => Real.exp (2*(B^(0.14 : ℝ)*Real.log B) -
      (a^2*c/(8*K^2))*B^(0.18 : ℝ))) atTop (𝓝 0) := by
  have hpos : 0 < a^2*c/(8*K^2) := by positivity
  convert sampling_union_bound_tendsto_zero hpos 2 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem sampling_sites_le_scale (U : ℝ) :
    ∀ᶠ B : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ U*B^(0.32 : ℝ) → (2 : ℝ)*N ≤ B := by
  have ht : Tendsto (fun B : ℝ => (2*U)*(B^(0.32 : ℝ)/B^((1 : ℝ)))) atTop (𝓝 0) := by
    simpa using (power_div_power_tendsto_zero (a := (0.32 : ℝ)) (b := 1)
      (by norm_num)).const_mul (2*U)
  have hh := ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hh,eventually_gt_atTop (0 : ℝ)] with B hlim hB
  intro N hN
  rw [Real.rpow_one] at hlim
  have he : 2*U*B^(0.32 : ℝ) < B := by
    rw [← mul_div_assoc] at hlim
    have h := (div_lt_iff₀ hB).mp hlim
    simpa using h
  nlinarith

theorem sampling_sample_size {B : ℝ} (hB : 1 ≤ B) :
    0 < ⌈B^(0.14 : ℝ)⌉₊ ∧
      B^(0.14 : ℝ) ≤ (⌈B^(0.14 : ℝ)⌉₊ : ℝ) ∧
      (⌈B^(0.14 : ℝ)⌉₊ : ℝ) ≤ 2*B^(0.14 : ℝ) := by
  have hp : 0 < B^(0.14 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans_le hB) _
  have hone : 1 ≤ B^(0.14 : ℝ) := Real.one_le_rpow hB (by norm_num)
  exact ⟨Nat.ceil_pos.mpr hp,Nat.le_ceil _,by linarith [Nat.ceil_lt_add_one hp.le]⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingRateEnvelope
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A vanishing error envelope for the adaptive cut comparison -/

namespace JointDickman
open Filter
open scoped Topology

theorem samplingDegreeEnvelope_tendsto (U q K : ℝ) :
    Tendsto (samplingDegreeEnvelope U q K) atTop (𝓝 0) := by
  unfold samplingDegreeEnvelope
  simpa only [mul_zero] using
    (power_div_power_tendsto_zero (a := (0.11 : ℝ)) (b := (0.14 : ℝ))
      (by norm_num)).const_mul (4*U*q/K^2)

theorem samplingSquareEnvelope_tendsto (q : ℝ) :
    Tendsto (samplingSquareEnvelope q) atTop (𝓝 0) := by
  unfold samplingSquareEnvelope
  simpa only [mul_zero] using
    (power_div_power_tendsto_zero (a := (0.20 : ℝ)) (b := (0.21 : ℝ))
      (by norm_num)).const_mul q

theorem samplingRateEnvelope_tendsto (C q U : ℝ) {c K a : ℝ}
    (hc : 0 < c) (hK : 0 < K) (ha : 0 < a) :
    Tendsto (samplingRateEnvelope C q c U K a) atTop (𝓝 0) := by
  unfold samplingRateEnvelope samplingEntropyEnvelope
  have hq : Tendsto (fun B : ℝ => C^2+q*B^(-0.21 : ℝ)) atTop (𝓝 (C^2)) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.21)).const_mul q)
  have hp := ((samplingDegreeEnvelope_tendsto U q K).add
    (samplingSquareEnvelope_tendsto q)).add (samplingFamily_envelope_tendsto hc hK ha)
  have hs := (hq.mul hp).sqrt
  simpa only [mul_zero,Real.sqrt_zero,add_zero,samplingEntropyEnvelope] using
    (sampling_error_envelope_tendsto U K c).add hs

theorem sampling_parameters_eventually (C q U L : ℝ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ B : ℝ in atTop, 1 ≤ B ∧ 2*C ≤ K*B^(0.07 : ℝ) ∧
      samplingDegreeEnvelope U q K B < 1 ∧
      Real.sqrt (q*B^(-0.21 : ℝ))+L*samplingDegreeEnvelope U q K B ≤ ε := by
  have hd : Tendsto (fun B : ℝ => K*B^(0.07 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).const_mul_atTop hK
  have hm : Tendsto (fun B : ℝ => Real.sqrt (q*B^(-0.21 : ℝ))+
      L*samplingDegreeEnvelope U q K B) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.21)).const_mul q).sqrt
    simpa using hh.add ((samplingDegreeEnvelope_tendsto U q K).const_mul L)
  filter_upwards [eventually_ge_atTop (1 : ℝ),hd.eventually_ge_atTop (2*C),
    (samplingDegreeEnvelope_tendsto U q K).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hm.eventually (eventually_lt_nhds hε)] with B hB hd hb hm
  exact ⟨hB,hd,hb,hm.le⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ScaledSamplingComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampling with the polynomial scales of the manuscript -/

namespace JointDickman
open Finset Classical PublishedInputs

theorem scaledSamplingComparison {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A] [DecidableEq A]
    (hMC : FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i b, 0 ≤ p i b) (hpone : ∀ i, ∑ b, p i b = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEsym : ∀ i j b z, E i j b z = E j i z b)
    (hHsym : ∀ i j b z, H i j b z = H j i z b)
    (hEdiag : ∀ i b, E i i b b = 0) (hHdiag : ∀ i b, H i i b b = 0)
    (hdom : ∀ i j b z, |E i j b z| ≤ H i j b z)
    {B C q c U K e L u a : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hc : 0 < c) (hU : 0 ≤ U) (hK : 0 < K) (hu : 0 ≤ u) (hL : 0 ≤ L) (ha : 0 < a)
    (hNlo : c*B^(0.32 : ℝ) ≤ Fintype.card ι)
    (hNhi : (Fintype.card ι : ℝ) ≤ U*B^(0.32 : ℝ))
    (hNsmall : (2 : ℝ)*Fintype.card ι ≤ B)
    (hgap : 2*C ≤ K*B^(0.07 : ℝ))
    (hbad : samplingDegreeEnvelope U q K B < 1)
    (hbound : e+Real.sqrt (q*B^(-0.21 : ℝ))+L*samplingDegreeEnvelope U q K B ≤ u)
    (hcut : u+a < L)
    (hmean : ∀ i b, |siteRowMean p H i b| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q*B^(-0.21 : ℝ))
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q*B^(-0.21 : ℝ))
    (htest : ∀ g h : ι → A → ℝ, (∀ i b, |g i b| ≤ 1) → (∀ i b, |h i b| ≤ 1) →
      siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e) :
    finiteExpectation (siteProductMass p) (fun x => kernelCutNorm (realizedSiteKernel E x)) ≤
      u+a+samplingRateEnvelope C q c U K a B := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd : 0 < K*B^(0.07 : ℝ) := by positivity
  have hg : C < K*B^(0.07 : ℝ) := by linarith
  have hb := sampling_degree_scale_bound hB0 hC hq hK hN.le hNhi hgap
  change _ ≤ samplingDegreeEnvelope U q K B at hb
  have hq0 : 0 ≤ q*B^(-0.21 : ℝ) := by positivity
  have hm := sampling_sample_size hB
  have hs := finiteSamplingComparison hMC p hp hpone E H hEsym hHsym hEdiag hHdiag hdom
    hC hq0 hd (by positivity : 0 < (Fintype.card ι : ℝ)*B^(-0.20 : ℝ)) hg hu hL ha
    hmean hsquareH hsquareE htest (hb.trans_lt hbad)
    ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hL)).trans hbound) hcut
    ⌈B^(0.14 : ℝ)⌉₊ hm.1
  have hsamp := samplingError_scale_bound hB hc hU hK.le hNlo hNhi
    ⌈B^(0.14 : ℝ)⌉₊ hm.2.1 hm.2.2
  have hfamily := samplingFamily_scale_bound (a := a) hB hc hK Fintype.card_pos
    hNlo hNsmall hm.2.2
  have hsquare : (Fintype.card ι : ℝ)*(q*B^(-0.21 : ℝ))/
      ((Fintype.card ι : ℝ)*B^(-0.20 : ℝ)) = samplingSquareEnvelope q B :=
    sampling_square_scale_eq hN.ne' hB0
  have htail := add_le_add (add_le_add hb hsquare.le) hfamily
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htail
    (add_nonneg (sq_nonneg C) hq0))
  unfold samplingRateEnvelope samplingEntropyEnvelope
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingComparisonLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform asymptotic sampling comparison -/

namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

/-- The manuscript's sampling transfer, uniformly over the finite site
spaces and all kernels satisfying its moment and fixed-test estimates.
No conditional second-moment bound at each row type is required. -/
theorem samplingComparison_eventually {C q c U e ε : ℝ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hc : 0 < c) (hU : 0 ≤ U)
    (he : 0 ≤ e) (hε : 0 < ε) :
    ∀ᶠ B : ℝ in atTop,
    ∀ (ι A : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A] [DecidableEq A],
    FiniteMcDiarmidInput ι A →
    ∀ (p : ι → A → ℝ), (∀ i b, 0 ≤ p i b) → (∀ i, ∑ b, p i b = 1) →
    ∀ (E H : ι → ι → A → A → ℝ),
    (∀ i j b z, E i j b z = E j i z b) →
    (∀ i j b z, H i j b z = H j i z b) →
    (∀ i b, E i i b b = 0) → (∀ i b, H i i b b = 0) →
    (∀ i j b z, |E i j b z| ≤ H i j b z) →
    c*B^(0.32 : ℝ) ≤ Fintype.card ι →
    (Fintype.card ι : ℝ) ≤ U*B^(0.32 : ℝ) →
    (∀ i b, |siteRowMean p H i b| ≤ C) →
    (∀ i, siteRowSquareMass p H i ≤ q*B^(-0.21 : ℝ)) →
    (∀ i, siteRowSquareMass p E i ≤ q*B^(-0.21 : ℝ)) →
    (∀ g h : ι → A → ℝ, (∀ i b, |g i b| ≤ 1) → (∀ i b, |h i b| ≤ 1) →
      siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e) →
    finiteExpectation (siteProductMass p) (fun x => kernelCutNorm (realizedSiteKernel E x)) ≤ e+ε := by
  let a := ε/4
  let L := e+ε+1
  have ha : 0 < a := by dsimp [a] <;> positivity
  have hL : 0 ≤ L := by dsimp [L] <;> linarith
  have hp := sampling_parameters_eventually C q U L (K := 1) (by norm_num) ha
  have hr := (samplingRateEnvelope_tendsto C q U hc (K := 1) (by norm_num) ha).eventually
    (eventually_lt_nhds (half_pos hε))
  filter_upwards [hp,hr,sampling_sites_le_scale U] with B hparams herr hsmall
  intro ι A _ _ _ _ _ hMC p hp hpone E H hEsym hHsym hEd hHd hdom hNlo hNhi hm hsH hsE ht
  have hb := scaledSamplingComparison hMC p hp hpone E H hEsym hHsym hEd hHd hdom
    hparams.1 hC hq hc hU (K := 1) (by norm_num)
    (u := e+a) (by linarith) hL ha hNlo hNhi (hsmall _ hNhi)
    hparams.2.1 hparams.2.2.1
    (by linarith [hparams.2.2.2])
    (by dsimp only [L,a] <;> linarith) hm hsH hsE ht
  dsimp only [a] at hb herr
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_KernelDifferenceMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Row-moment bounds for the error between two finite kernels -/
namespace JointDickman
open Finset PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

theorem siteRowMean_add (p : ι → A → ℝ) (K J : ι → ι → A → A → ℝ)
    (i : ι) (a : A) :
    siteRowMean p (fun i j a b => K i j a b+J i j a b) i a =
      siteRowMean p K i a+siteRowMean p J i a := by
  simp only [siteRowMean,finiteExpectation_add,sum_add_distrib]

theorem siteRowSquareMass_add_le (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (K J : ι → ι → A → A → ℝ) (i : ι) :
    siteRowSquareMass p (fun i j a b => K i j a b+J i j a b) i ≤
      2*siteRowSquareMass p K i+2*siteRowSquareMass p J i := by
  unfold siteRowSquareMass
  calc
    _ ≤ finiteExpectation (p i) (fun a => ∑ j : {j : ι // j ≠ i},
        finiteExpectation (p j) (fun b => 2*(K i j a b)^2+2*(J i j a b)^2)) := by
      apply finiteExpectation_mono (p i) (hp i)
      intro a
      apply sum_le_sum
      intro j _
      apply finiteExpectation_mono (p j) (hp j)
      intro b
      nlinarith [sq_nonneg (K i j a b-J i j a b)]
    _ = _ := by
      simp only [finiteExpectation_add,finiteExpectation_const_mul,sum_add_distrib,← mul_sum]

theorem siteRowSquareMass_sub_le (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (K J : ι → ι → A → A → ℝ) (i : ι) :
    siteRowSquareMass p (fun i j a b => K i j a b-J i j a b) i ≤
      2*siteRowSquareMass p K i+2*siteRowSquareMass p J i := by
  unfold siteRowSquareMass
  calc
    _ ≤ finiteExpectation (p i) (fun a => ∑ j : {j : ι // j ≠ i},
        finiteExpectation (p j) (fun b => 2*(K i j a b)^2+2*(J i j a b)^2)) := by
      apply finiteExpectation_mono (p i) (hp i)
      intro a
      apply sum_le_sum
      intro j _
      apply finiteExpectation_mono (p j) (hp j)
      intro b
      nlinarith [sq_nonneg (K i j a b+J i j a b)]
    _ = _ := by
      simp only [finiteExpectation_add,finiteExpectation_const_mul,sum_add_distrib,← mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingErrorEnvelope
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive sampling envelope for the latent-minus-model error -/
namespace JointDickman
open Finset PublishedInputs

theorem addLagEnvelope_dominates {M T : ℕ} {A : Type*} {D : ℝ}
    (K J : Fin M → Fin M → A → A → ℝ)
    (hK : ∀ i k a b, 0 ≤ K i k a b)
    (hJ : ∀ i k a b, |J i k a b| ≤ lagEnvelope T D i k)
    (i k : Fin M) (a b : A) :
    |K i k a b-J i k a b| ≤ addLagEnvelope K T D i k a b := by
  exact (abs_sub _ _).trans (add_le_add
    (le_of_eq (abs_of_nonneg (hK i k a b))) (hJ i k a b))

theorem addLagEnvelope_moments {M T : ℕ} {A : Type*} [Fintype A]
    (hT : 0 < T) {D C q : ℝ} (hD : 0 ≤ D)
    (p : Fin M → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K J : Fin M → Fin M → A → A → ℝ)
    (hJ : ∀ i k a b, |J i k a b| ≤ lagEnvelope T D i k)
    (hrow : ∀ i a, |siteRowMean p K i a| ≤ C)
    (hquad : ∀ i, siteRowSquareMass p K i ≤ q) :
    (∀ i a, |siteRowMean p (addLagEnvelope K T D) i a| ≤ C+2*D*Real.exp 24) ∧
    (∀ i, siteRowSquareMass p (addLagEnvelope K T D) i ≤ q*2+4*D^2*Real.exp 1200/(T : ℝ)) ∧
    (∀ i, siteRowSquareMass p (fun i k a b => K i k a b-J i k a b) i ≤
      q*2+4*D^2*Real.exp 1200/(T : ℝ)) := by
  let F : Fin M → Fin M → A → A → ℝ := fun i k _ _ => lagEnvelope T D i k
  have hF (i k : Fin M) (a b : A) : |F i k a b| ≤ lagEnvelope T D i k := by
    dsimp only [F]
    rw [abs_of_nonneg (lagEnvelope_nonneg T hD i k)]
  have hFsq (i : Fin M) := lagEnvelope_row_square_mass hT hD p hp hpone F hF i
  have hJsq (i : Fin M) := lagEnvelope_row_square_mass hT hD p hp hpone J hJ i
  refine ⟨?_,?_,?_⟩
  · intro i a
    change |siteRowMean p (fun i k a b => K i k a b+F i k a b) i a| ≤ _
    rw [siteRowMean_add]
    exact (abs_add_le _ _).trans
      (add_le_add (hrow i a) (lagEnvelope_row_mean hT hD p hp hpone F hF i a))
  · intro i
    change siteRowSquareMass p (fun i k a b => K i k a b+F i k a b) i ≤ _
    have h := (siteRowSquareMass_add_le p hp K F i).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hquad i) (by norm_num))
        (mul_le_mul_of_nonneg_left (hFsq i) (by norm_num)))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro i
    have h := (siteRowSquareMass_sub_le p hp K J i).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hquad i) (by norm_num))
        (mul_le_mul_of_nonneg_left (hJsq i) (by norm_num)))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingLagModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampling transfer for a model controlled by the singular-factor lag envelope -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem sampling_lag_model {C q D c U e ε : ℝ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hD : 0 ≤ D) (hc : 0 < c) (hU : 0 ≤ U)
    (he : 0 ≤ e) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ (M : ℕ) (A : Type*) [Fintype A] [DecidableEq A],
      0 < M → FiniteMcDiarmidInput (Fin M) A →
      ∀ (p : Fin M → A → ℝ), (∀ i a, 0 ≤ p i a) → (∀ i, ∑ a, p i a = 1) →
      ∀ (K J : Fin M → Fin M → A → A → ℝ),
      (∀ i j a b, K i j a b = K j i b a) → (∀ i j a b, J i j a b = J j i b a) →
      (∀ i a, K i i a a = 0) → (∀ i a, J i i a a = 0) →
      (∀ i j a b, 0 ≤ K i j a b) →
      (∀ i j a b, |J i j a b| ≤ lagEnvelope (amplificationMultiplier B) D i j) →
      c*(B : ℝ)^(0.32 : ℝ) ≤ M → (M : ℝ) ≤ U*(B : ℝ)^(0.32 : ℝ) →
      (∀ i a, |siteRowMean p K i a| ≤ C) →
      (∀ i, siteRowSquareMass p K i ≤ q*(B : ℝ)^(-0.21 : ℝ)) →
      (∀ g h : Fin M → A → ℝ, (∀ i a, |g i a| ≤ 1) → (∀ i a, |h i a| ≤ 1) →
        siteTestMean p (fun i j a b => K i j a b-J i j a b) g h ≤ (M : ℝ)*e) →
      finiteExpectation (siteProductMass p) (fun x =>
        kernelCutNorm (realizedSiteKernel (fun i j a b => K i j a b-J i j a b) x)) ≤ e+ε := by
  have hs := (samplingComparison_eventually
    (show 0 ≤ C+2*D*Real.exp 24 by positivity)
    (show 0 ≤ 2*q+1 by positivity) hc hU he hε)
  have hsNat := tendsto_natCast_atTop_atTop.eventually hs
  filter_upwards [hsNat,amplification_inverse_square_rate (4*D^2*Real.exp 1200),
    amplificationMultiplier_comparable] with B hs hsmall hT
  intro M A _ _ hM hMC p hp hpone K J hKsym hJsym hKd hJd hKpos hJbound hMlo hMhi hrow hquad htest
  have : NeZero M := ⟨hM.ne'⟩
  let E := fun i j a b => K i j a b-J i j a b
  let H := addLagEnvelope K (amplificationMultiplier B) D
  obtain ⟨hHrow,hHquad,hEquad⟩ := addLagEnvelope_moments hT.1 hD p hp hpone K J hJbound hrow hquad
  have hquadBound : q*(B : ℝ)^(-0.21 : ℝ)*2+4*D^2*Real.exp 1200/(amplificationMultiplier B : ℝ) ≤
      (2*q+1)*(B : ℝ)^(-0.21 : ℝ) := by
    have hsmall' : 4*D^2*Real.exp 1200/(amplificationMultiplier B : ℝ) ≤ (B : ℝ)^(-0.21 : ℝ) := by
      convert hsmall using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    nlinarith
  apply hs (Fin M) A hMC p hp hpone E H
  · intro i j a b
    dsimp only [E]
    rw [hKsym,hJsym]
  · intro i j a b
    simp only [H,addLagEnvelope,hKsym i j a b,lagEnvelope,ne_comm,Nat.dist_comm]
  · intro i a
    simp only [E,hKd,hJd,sub_self]
  · intro i a
    simp only [H,addLagEnvelope,hKd,lagEnvelope,ne_eq,not_true_eq_false,false_and,ite_false, if_false,add_zero]
  · exact addLagEnvelope_dominates K J hKpos hJbound
  · simpa only [Fintype.card_fin] using hMlo
  · simpa only [Fintype.card_fin] using hMhi
  · exact hHrow
  · intro i
    exact (hHquad i).trans hquadBound
  · intro i
    exact (hEquad i).trans hquadBound
  · simpa only [Fintype.card_fin] using htest

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSampling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampling the actual latent counting graph and its finite-feature model -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_sampling_jd_oai
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) {L : ℕ} {η cap : ℝ} (hL : 10000 ≤ L) (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ w c₁ U₁ ε : ℝ, 0 < w → 0 < c₁ → 0 ≤ U₁ → 0 < ε →
      ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ Cmin : ℝ, 0 ≤ Cmin ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (H M U V Q : ℕ),
        Cmin ≤ C →
        (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
            (dyadicBoxUpper B (amplificationMultiplier B)),
          ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
            (dyadicBoxUpper B (amplificationMultiplier B)),
          ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/amplificationMultiplier B)⌋₊ ≤ V) →
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → amplificationMultiplier B*Q ≤ B →
        η*amplificationMultiplier B ≤ H → amplificationMultiplier B ≤ M →
        c₁*(B : ℝ)^(0.32 : ℝ) ≤ M → (M : ℝ) ≤ U₁*(B : ℝ)^(0.32 : ℝ) →
        FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset →
        ∀ σ : ℝ, |σ| ≤ 3 →
        finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
          (fun x => kernelCutNorm (realizedSiteKernel
            (countingSiteError P m B L (amplificationMultiplier B) H M τ C w c D σ) x)) ≤ ε := by
  obtain ⟨τ,q,hτ,hτcap,hτsmall,hq,hquad⟩ :=
    latentPrimeSiteKernel_row_square_mass_jd hFord hM hL (show 0 < η/2 by positivity) hcap
  obtain ⟨R,hR,hroot⟩ := independentRootMean_bounded hM
  obtain ⟨J,hJ,hrow⟩ := latentPrimeSiteKernel_row_mean_jd hFord hM
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro w c₁ U₁ ε hw hc₁ hU₁ hε
  let δ := ε/(12*Real.exp 24)
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  obtain ⟨K,hK,P,c,hc,D,m,hm,C₀,hC₀,e,he0,he,hblock⟩ :=
    counting_block_test_jd hFord hSD hSW hM hMP (by omega : 0 < L) hτ hη hw hδ
  let Cmin := max 0 (10*Real.log ((K+1)/δ))
  have hCmin : 0 ≤ Cmin := le_max_left _ _
  have htail : ∀ C : ℝ, Cmin ≤ C → K*Real.exp (-(1/10 : ℝ)*C) ≤ δ := by
    intro C hC
    have hh : 10*Real.log ((K+1)/δ) ≤ C := (le_max_right _ _).trans hC
    have hexp := Real.exp_le_exp.mpr (show -(1/10 : ℝ)*C ≤ -Real.log ((K+1)/δ) by linarith)
    calc
      _ ≤ (K+1)*Real.exp (-(1/10 : ℝ)*C) := by gcongr; linarith
      _ ≤ (K+1)*Real.exp (-Real.log ((K+1)/δ)) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
      _ = δ := by
        rw [Real.exp_neg,Real.exp_log (by positivity : 0 < (K+1)/δ)]
        field_simp
  have hsample := sampling_lag_model hJ.le hq.le
    (show 0 ≤ R*C₀/η by positivity) hc₁ hU₁ (show 0 ≤ ε/2 by positivity)
    (show 0 < ε/2 by positivity)
  refine ⟨P,c,hc,D,m,hm,Cmin,hCmin,?_⟩
  filter_upwards [hquad,hroot,hrow,hblock,hsample,amplification_sampling_scale,
    he.eventually (eventually_le_nhds hδ)] with B hquad hroot hrow hblock hsample hscale heB
  intro C H M U V Q hC hU hV hdyU hdyV hQ hcut hTQ hH hTM hMlo hMhi hMC σ hσ
  let T := amplificationMultiplier B
  have hT : 0 < T := hscale.1
  have hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) := hscale.2.1
  have hH' : (η/2)*(B : ℝ)^(32/100 : ℝ) ≤ H := by
    calc
      _ = η*((B : ℝ)^(32/100 : ℝ)/2) := by ring
      _ ≤ η*(T : ℝ) := mul_le_mul_of_nonneg_left hscale.2.2.2.2.2 hη.le
      _ ≤ _ := hH
  have hMpos : 0 < M := hT.trans_le hTM
  have hχ := rampedCandidateCutoff_bounds hw B T σ (M := M)
  obtain ⟨hbound,htest⟩ := hblock C T H M U V Q (hCmin.trans hC) hT le_rfl
    hscale.2.2.2.2.1 hU hV hdyU hdyV hQ hcut hTQ hH hTM σ hσ
  have htestsmall : 2*(e B+K*Real.exp (-(1/10 : ℝ)*C)+δ)*Real.exp 24 ≤ ε/2 := by
    calc
      _ ≤ 2*(δ+δ+δ)*Real.exp 24 := by gcongr; exact htail C hC
      _ = _ := by dsimp [δ]; field_simp <;> ring
  have hs := hsample M (auxiliaryPrimes B).powerset hMpos hMC
    (fun _ : Fin M => independentPrimeSetMass B)
    (fun _ => independentPrimeSetMass_nonneg B) (fun _ => independentPrimeSetMass_sum B)
    (latentPrimeSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ))
    (countingSiteModel P m B L T H M τ C c D σ)
    (fun i j a b => candidateSiteKernel_symm _ _ _ _ _ _ _ _ _ _ _ _)
    (countingSiteModel_symm P m B L T H M τ C c D σ)
    (fun i a => candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _)
    (fun i a => countingSiteModel_diag P m B L T H M τ C c D σ i a a)
    (fun i j a b => candidateSiteKernel_nonneg _ _ _ _ _ _ _ _
      (fun e => (hχ e).1) _ _ _ _)
    (countingSiteModel_uniform_envelope hMP P m B L T H M τ C c D hT hη hC₀
      (hroot L τ C) hH hbound) hMlo hMhi
    (hrow L T H M τ C hT hTs _ hχ)
    (by simpa only [show -(21/100 : ℝ) = (-0.21 : ℝ) by norm_num] using
      hquad T H M C hT hTs hscale.2.2.1 hscale.2.2.2.1 hH' _ hχ)
    (fun g h hg hh => (htest g h hg hh).trans
      (mul_le_mul_of_nonneg_left htestsmall (Nat.cast_nonneg M)))
  change finiteExpectation _ (fun x => kernelCutNorm
    (realizedSiteKernel (countingSiteError P m B L T H M τ C w c D σ) x)) ≤ ε/2+ε/2 at hs
  rw [add_halves] at hs
  exact hs

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.counting_sampling_jd_oai := @OAI.JointDickman.counting_sampling_jd_oai
