-- Prove2me | solution 1 for OAI.JointDickman.counting_block_test_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:10:15.539662+00:00
-- url     : https://prove2.me/submissions/66d83576-0e71-46eb-b7b4-55d7fef66bb6

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_amplification_positive_mass_bound_jd
import Theorems.Thm_OAI_JointDickman_counting_arithmetic_feature_comparison_jd
import Theorems.Thm_OAI_JointDickman_weighted_candidate_coefficient_removal_jd

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

/-- Every smaller real power is negligible compared with a larger one. -/
theorem power_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => B ^ a / B ^ b) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [← Real.rpow_sub hB]
  congr 1
  ring

/-- In particular, each fixed polynomial degree below the cutoff exponent
is negligible compared with `P₀ = B^1000`. -/
theorem polynomial_div_primeCutoff_tendsto_zero {k : ℕ} (hk : k < 1000) :
    Tendsto (fun B : ℝ => B ^ k / B ^ (1000 : ℕ)) atTop (𝓝 0) := by
  have h : (k : ℝ) < (1000 : ℝ) := by exact_mod_cast hk
  have hlim := power_div_power_tendsto_zero h
  change Tendsto (fun B : ℝ => B ^ (k : ℝ) / B ^ ((1000 : ℕ) : ℝ))
    atTop (𝓝 0) at hlim
  simpa only [Real.rpow_natCast] using hlim

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

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

theorem primeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    primeProductMass P z (∏ p ∈ S, p) =
      bernoulliSubsetMass P (fun p => z / p) S := by
  classical
  unfold primeProductMass
  rw [Finset.sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (Finset.mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (Finset.mem_powerset.mpr hS))

/-- The coefficient and remaining-site weight convert a sum over divisors
into a fair-split expectation, with total normalization `L * R`. -/
theorem fairSplit_weight_identity {α : Type*} [DecidableEq α]
    {S T : Finset α} (hT : T ⊆ S) (L R : ℝ) (hR : 0 ≤ R) :
    (L * Real.sqrt R * (1 / 2 : ℝ) ^ T.card) *
        (Real.sqrt R * (1 / 2 : ℝ) ^ (S \ T).card) =
      L * R * (1 / 2 : ℝ) ^ S.card := by
  calc
    _ = L * (Real.sqrt R * Real.sqrt R) *
        ((1 / 2 : ℝ) ^ T.card * (1 / 2 : ℝ) ^ (S \ T).card) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt hR, ← pow_add, add_comm T.card,
        Finset.card_sdiff_add_card_eq_card hT]

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- The Mertens remainder tends to its additive constant. -/
theorem primeReciprocalSum_remainder_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ M : ℝ, Tendsto (fun x : ℝ => primeReciprocalSum x - Real.log (Real.log x))
      atTop (𝓝 M) := by
  obtain ⟨M, C, _, hC⟩ := hM
  refine ⟨M, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hlim : Tendsto (fun x : ℝ => C / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa [Real.norm_eq_abs, primeReciprocalSum, primesLE_eq_filter] using hC x hx

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeHarmonicWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact harmonic weights of squarefree prime products

The uncorrected independent-prime mass is the harmonic rough coefficient,
including the empty product. This identifies the weight used in partial summation.
-/

namespace JointDickman

open Finset ArithmeticFunction

theorem primeProduct_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
  · exact fun p hp => (hS p hp).squarefree

theorem primeProduct_cardFactors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    cardFactors (∏ p ∈ S, p) = S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hpprime := hS p (mem_insert_self p S)
      have hrest : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
      rw [prod_insert hp, cardFactors_mul hpprime.ne_zero
        (prod_ne_zero_iff.mpr (fun q hq => (hrest q hq).ne_zero)),
        cardFactors_apply_prime hpprime, ih hrest, card_insert_of_notMem hp]
      omega

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

theorem auxiliaryRatio_tendsto : Tendsto auxiliaryRatio atTop atTop := by
  have hlim : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ)))
      atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul 1000
  have hpos : ∀ᶠ B : ℕ in atTop, 0 < 1000 * (Real.log B / (B : ℝ)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
    exact mul_pos (by norm_num) (div_pos (Real.log_pos hBreal) (by linarith))
  have hgt : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ)))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hlim, hpos⟩
  convert hgt.inv_tendsto_nhdsGT_zero using 1
  all_goals try with_reducible_and_instances rfl
  ext B
  simp only [auxiliaryRatio, Pi.inv_apply, mul_inv_rev, inv_div]
  ring

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

theorem auxiliaryRatio_mul_log {B : ℕ} (hB : 1 < B) :
    auxiliaryRatio B * Real.log (auxiliaryCutoff B) = B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hlog : Real.log B ≠ 0 := (Real.log_pos hBreal).ne'
  simp only [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  norm_num
  field_simp

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

theorem coefficientScale_eventually_le : ∀ᶠ B : ℕ in atTop, coefficientScale B ≤ B := by
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 1] with B hR hB
  have hp : auxiliaryRatio B ^ (1 / 2 : ℝ) ≤ auxiliaryRatio B := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1 / 2 : ℝ) ≤ 1))
  calc
    coefficientScale B ≤ Real.log (auxiliaryCutoff B) * auxiliaryRatio B :=
      mul_le_mul_of_nonneg_left hp (Real.log_natCast_nonneg _)
    _ = B := by rw [mul_comm, auxiliaryRatio_mul_log hB]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the coefficient scale in the sieve density -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem sieveCutoff_eventually {c : ℝ} (hc : 0 < c) :
    ∀ᶠ B : ℕ in atTop, 2 ≤ sieveCutoff c B ∧ auxiliaryCutoff B ≤ sieveCutoff c B ∧
      (c / 2) * B ≤ Real.log (sieveCutoff c B) ∧
      (sieveCutoff c B : ℝ) ≤ Real.exp (c * B) := by
  have hlarge : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.exp ((c / 2) * B) :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith : 0 < c / 2))).eventually_ge_atTop 2
  have hpoly : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ 1000 ≤ Real.exp ((c / 2) * B) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 1000 (by linarith : 0 < c / 2)).def
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with B hB
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg B : (0 : ℝ) ≤ B) 1000),
      abs_of_pos (Real.exp_pos _), one_mul] using hB
  filter_upwards [hlarge, hpoly] with B hlargeB hpolyB
  have hfloor : Real.exp ((c / 2) * B) ≤ (sieveCutoff c B : ℝ) := by
    have heq : Real.exp (c * B) = Real.exp ((c / 2) * B) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h := Nat.lt_floor_add_one (Real.exp (c * B))
    change Real.exp (c * B) < (sieveCutoff c B : ℝ) + 1 at h
    rw [heq] at h
    nlinarith
  refine ⟨?_, ?_, ?_, Nat.floor_le (Real.exp_pos _).le⟩
  · exact_mod_cast hlargeB.trans hfloor
  · have h := hpolyB.trans hfloor
    exact_mod_cast h
  · have h := Real.log_le_log (Real.exp_pos ((c / 2) * B)) hfloor
    simpa only [Real.log_exp] using h

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

/-- On nonzero integers the dividing-prime set is exactly the intersection
with the integer's finite prime-factor set. -/
theorem coefficientPrimeSet_eq_inter {B n : ℕ} (hn : n ≠ 0) :
    coefficientPrimeSet B n = n.primeFactors ∩ auxiliaryPrimes B := by
  classical
  ext p
  simp only [coefficientPrimeSet, mem_filter, mem_inter]
  constructor
  · rintro ⟨hp, hpn⟩
    exact ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.mem_primeFactors hpn hn, hp⟩
  · rintro ⟨hp, hP⟩
    exact ⟨hP, (Nat.mem_primeFactors.mp hp).2.1⟩

theorem primePrefix_inter (B : ℕ) (g : ℝ) (S T : Finset ℕ) :
    primePrefix B g (S ∩ T) = S ∩ primePrefix B g T := by
  classical
  unfold primePrefix
  split_ifs
  · ext p
    simp only [mem_filter, mem_inter]
    tauto
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

theorem fairRetentionBitMass_marginal (q : ℝ) (b : Bool) :
    (∑ hit, bernoulliBitMass q hit * fairRetentionBitMass hit b) = bernoulliBitMass (q / 2) b := by
  cases b <;> simp [fairRetentionBitMass, bernoulliBitMass] <;> ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SelectedPrimeOdds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform odds corrections on bounded prime products -/

namespace JointDickman

open Finset

theorem selectedPrime_card_log_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (S.card : ℝ) * Real.log 2 ≤ Real.log (∏ p ∈ S, p : ℕ) := by
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).ne_zero)]
  calc
    _ = ∑ _p ∈ S, Real.log 2 := by simp
    _ ≤ _ := sum_le_sum (fun p hp => Real.log_le_log (by norm_num)
      (by exact_mod_cast (hS p hp).two_le))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryLogarithms
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic scales for the regularity grid -/

namespace JointDickman

open Filter
open scoped Topology

theorem auxiliaryLogLength_tendsto : Tendsto auxiliaryLogLength atTop atTop :=
  Real.tendsto_log_atTop.comp auxiliaryRatio_tendsto

theorem log_auxiliaryCutoff (B : ℕ) :
    Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
  simp [auxiliaryCutoff, Nat.cast_pow, Real.log_pow]

theorem auxiliaryLogLength_eq {B : ℕ} (hB : 1 < B) :
    auxiliaryLogLength B = Real.log B - Real.log 1000 - Real.log (Real.log B) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlog : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [auxiliaryLogLength, auxiliaryRatio, Real.log_div hB0.ne' (mul_pos (by norm_num) hlog).ne',
    Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hlog.ne']
  ring

theorem logLogCutoff_div_log_tendsto_zero :
    Tendsto (fun B : ℕ => Real.log (Real.log (auxiliaryCutoff B)) / Real.log B) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop)
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hconst : Tendsto (fun B : ℕ => Real.log 1000 / Real.log B) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have h := hconst.add hsmall
  norm_num only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [log_auxiliaryCutoff, Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hl.ne', add_div]
  rfl

theorem auxiliaryLogLength_div_log_tendsto :
    Tendsto (fun B : ℕ => auxiliaryLogLength B / Real.log B) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub logLogCutoff_div_log_tendsto_zero
  norm_num only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [auxiliaryLogLength_eq hB, log_auxiliaryCutoff,
    Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hl.ne']
  field_simp
  ring

theorem log_div_auxiliaryLogLength_tendsto :
    Tendsto (fun B : ℕ => Real.log B / auxiliaryLogLength B) atTop (𝓝 1) := by
  have h := auxiliaryLogLength_div_log_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div, inv_one] using h

theorem logLogCutoff_div_auxiliaryLogLength_tendsto_zero :
    Tendsto (fun B : ℕ => Real.log (Real.log (auxiliaryCutoff B)) / auxiliaryLogLength B) atTop (𝓝 0) := by
  have h := logLogCutoff_div_log_tendsto_zero.mul log_div_auxiliaryLogLength_tendsto
  norm_num only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : Real.log B ≠ 0 := (Real.log_pos (by exact_mod_cast hB)).ne'
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularityPrimeSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens sums at the prefix scales used by regularity -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryCutoff_le_exp_rpow {c g : ℝ} (hc : 0 < c) (hg : 0 < g) :
    ∀ᶠ B : ℕ in atTop, (auxiliaryCutoff B : ℝ) ≤ Real.exp (c * (B : ℝ) ^ g) := by
  have hlim : Tendsto (fun B : ℕ => (1000 / c) * (Real.log B / (B : ℝ) ^ g)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((isLittleO_log_rpow_atTop hg).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul (1000 / c)
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hpow : 0 < (B : ℝ) ^ g := Real.rpow_pos_of_pos hB0 g
  have hsmall' : 1000 * Real.log B ≤ c * (B : ℝ) ^ g := by
    have hh : (1000 * Real.log B) / (c * (B : ℝ) ^ g) ≤ 1 := by
      convert hsmall using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
    exact (div_le_one (mul_pos hc hpow)).mp hh
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast pow_pos (by omega : 0 < B) 1000
  calc
    _ = Real.exp (Real.log (auxiliaryCutoff B)) := (Real.exp_log hP).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [log_auxiliaryCutoff] using hsmall')

/-- Both interior prefixes and the full fixed exponential cutoff have
normalized reciprocal-prime mass g; the endpoint multiplier c contributes
only a bounded logarithm. -/
theorem regularity_prefix_prime_sum_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c g : ℝ}
    (hc : 0 < c) (hg : 0 < g) :
    Tendsto (fun B : ℕ =>
      (∑ p ∈ largePrimeSet (Real.exp (c * (B : ℝ) ^ g)) (auxiliaryCutoff B), 1 / (p : ℝ)) /
        auxiliaryLogLength B) atTop (𝓝 g) := by
  obtain ⟨M, hrem⟩ := primeReciprocalSum_remainder_tendsto hM
  have hpow : Tendsto (fun B : ℕ => c * (B : ℝ) ^ g) atTop atTop :=
    ((tendsto_rpow_atTop hg).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hupper := Real.tendsto_exp_atTop.comp hpow
  have hcut : Tendsto (fun B : ℕ => (auxiliaryCutoff B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto
  have herr : Tendsto (fun B : ℕ =>
      ((primeReciprocalSum (Real.exp (c * (B : ℝ) ^ g)) - Real.log (Real.log (Real.exp (c * (B : ℝ) ^ g)))) -
        (primeReciprocalSum (auxiliaryCutoff B) - Real.log (Real.log (auxiliaryCutoff B)))) /
          auxiliaryLogLength B) atTop (𝓝 0) :=
    ((hrem.comp hupper).sub (hrem.comp hcut)).div_atTop auxiliaryLogLength_tendsto
  have hconst : Tendsto (fun B : ℕ => Real.log c / auxiliaryLogLength B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop auxiliaryLogLength_tendsto
  have hmain := (hconst.add (log_div_auxiliaryLogLength_tendsto.const_mul g)).sub
    logLogCutoff_div_auxiliaryLogLength_tendsto_zero
  have h := herr.add hmain
  norm_num only [zero_add, mul_one, sub_zero] at h
  apply h.congr'
  filter_upwards [auxiliaryCutoff_le_exp_rpow hc hg, eventually_gt_atTop 1] with B hPY hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  rw [largePrimeSet_reciprocal_eq (Nat.cast_nonneg _) hPY, Real.log_exp,
    Real.log_mul hc.ne' (Real.rpow_pos_of_pos hB0 g).ne', Real.log_rpow hB0]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ChernoffParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative choices for the regularity Chernoff bounds -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem exists_prefix_tilt {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ τ ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ g : ℝ, 0 ≤ g → g ≤ 1 →
        -s * τ + (g / 2) * (Real.exp s - 1 - s) ≤ -s * τ / 2 ∧
        -s * τ + (g / 2) * (Real.exp (-s) - 1 + s) ≤ -s * τ / 2 := by
  let s := min τ (1 / 10 : ℝ)
  have hs : 0 < s := lt_min hτ (by norm_num)
  have hsτ : s ≤ τ := min_le_left _ _
  have hs1 : s ≤ 1 / 10 := min_le_right _ _
  have hp := Real.abs_exp_sub_one_sub_id_le (show |s| ≤ 1 by rw [abs_of_pos hs]; linarith)
  have hn := Real.abs_exp_sub_one_sub_id_le (show |-s| ≤ 1 by rw [abs_neg, abs_of_pos hs]; linarith)
  have hp0 : 0 ≤ Real.exp s - 1 - s := by linarith [Real.add_one_le_exp s]
  have hn0 : 0 ≤ Real.exp (-s) - 1 + s := by linarith [Real.add_one_le_exp (-s)]
  have hp2 := (abs_le.mp hp).2
  have hn2 := (abs_le.mp hn).2
  refine ⟨s, hs, hsτ, hs1, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (s - 1 / 10)]
  · calc
      Real.exp (-s) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 2 := by norm_num
  · intro g hg hg1
    have hst := mul_nonneg hs.le (sub_nonneg.mpr hsτ)
    constructor
    · have hmul := mul_nonneg (sub_nonneg.mpr hg1) hp0
      nlinarith
    · have hmul := mul_nonneg (sub_nonneg.mpr hg1) hn0
      nlinarith

theorem tail_tilt_margin :
    0 < (1 / 2 : ℝ) * (1 - Real.exp (-(1 / 10 : ℝ))) - (2 / 5 : ℝ) * (1 / 10) := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (show |-(1 / 10 : ℝ)| ≤ 1 by norm_num))).2
  norm_num at h ⊢
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularityTailPrimeSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform lower bound for reciprocal-prime tail masses -/

namespace JointDickman

open Finset

theorem regularity_tail_prime_sum_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ B X Y : ℝ, 0 < B → 2 ≤ X → c * B ≤ Real.log X → 1 ≤ Y →
      Real.log (B / Y) - K ≤ ∑ p ∈ largePrimeSet X (Real.exp Y), 1 / (p : ℝ) := by
  obtain ⟨C, hC, hm⟩ := prime_interval_mertens_error hM
  refine ⟨2 * C + |Real.log c|, by positivity, ?_⟩
  intro B X Y hB hX hlog hY
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hEY : 2 ≤ Real.exp Y := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr hY
  have hlogB : Real.log (c * B) = Real.log c + Real.log B :=
    Real.log_mul hc.ne' hB.ne'
  by_cases hYX : Real.exp Y ≤ X
  · have hlogXY : Y ≤ Real.log X := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos Y) hYX
    have hlogX1 : 1 ≤ Real.log X := hY.trans hlogXY
    have herr := hm (Real.exp Y) X hEY hYX
    rw [Real.log_exp] at herr
    have hCY : C / Y ≤ C := div_le_self hC hY
    have hCX : C / Real.log X ≤ C := div_le_self hC hlogX1
    have hcompare : Real.log c + Real.log B ≤ Real.log (Real.log X) := by
      rw [← hlogB]
      exact Real.log_le_log (mul_pos hc hB) hlog
    rw [Real.log_div hB.ne' hY0.ne']
    have hlo := (abs_le.mp herr).1
    have habs := neg_abs_le (Real.log c)
    linarith
  · have hXY : X < Real.exp Y := lt_of_not_ge hYX
    have hlogXY : Real.log X < Y := by
      simpa only [Real.log_exp] using Real.log_lt_log hX0 hXY
    have hcompare : Real.log c + Real.log B ≤ Real.log Y := by
      rw [← hlogB]
      exact Real.log_le_log (mul_pos hc hB) (hlog.trans hlogXY.le)
    have hsum : 0 ≤ ∑ p ∈ largePrimeSet X (Real.exp Y), 1 / (p : ℝ) :=
      sum_nonneg (fun _ _ => by positivity)
    rw [Real.log_div hB.ne' hY0.ne']
    have habs := neg_abs_le (Real.log c)
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DyadicTailSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the lower-tail Chernoff bounds over dyadic endpoints -/

namespace JointDickman

open Finset

theorem geometric_sum_under_cap (S : Finset ℕ) {r w : ℝ}
    (hr : 1 < r) (hw : 0 ≤ w) (hcap : ∀ i ∈ S, w * r ^ i ≤ 1) :
    (∑ i ∈ S, w * r ^ i) ≤ r / (r - 1) := by
  classical
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hm : m ∈ S := S.max'_mem hS
    have hsub : S ⊆ range (m + 1) := by
      intro i hi
      exact mem_range.mpr (Nat.lt_succ_of_le (S.le_max' i hi))
    have hsum : (∑ i ∈ range (m + 1), w * r ^ i) * (r - 1) = w * (r ^ (m + 1) - 1) := by
      rw [← mul_sum, mul_assoc, geom_sum_mul]
    have hlast := hcap m hm
    calc
      _ ≤ ∑ i ∈ range (m + 1), w * r ^ i := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ r / (r - 1) := by
        apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
        rw [hsum, pow_succ]
        have h := mul_le_mul_of_nonneg_right hlast (by linarith : 0 ≤ r)
        nlinarith
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp only [he, sum_empty]
    positivity

theorem dyadic_power_sum_bound (S : Finset ℕ) {B Y a : ℝ}
    (hB : 0 < B) (hY : 0 ≤ Y) (ha : 0 < a)
    (hcap : ∀ i ∈ S, (2 : ℝ) ^ i * Y ≤ B) :
    (∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ a) ≤
      (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) := by
  have heq (i : ℕ) : (((2 : ℝ) ^ i * Y) / B) ^ a =
      (Y / B) ^ a * ((2 : ℝ) ^ a) ^ i := by
    rw [mul_div_assoc, Real.mul_rpow (by positivity) (div_nonneg hY hB.le),
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  simp_rw [heq]
  apply geometric_sum_under_cap S (Real.one_lt_rpow (by norm_num) ha) (Real.rpow_nonneg (div_nonneg hY hB.le) _)
  intro i hi
  rw [← heq]
  have hle : ((2 : ℝ) ^ i * Y) / B ≤ 1 := (div_le_one hB).mpr (hcap i hi)
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ ((2 : ℝ) ^ i * Y) / B) hle ha.le
  simpa only [Real.one_rpow] using h

theorem tailSaving_pos : 0 < tailSaving := tail_tilt_margin

theorem tail_chernoff_factor_bound {B Y M K C : ℝ}
    (hB : 0 < B) (hY : 0 < Y) (hM : Real.log (B / Y) - K ≤ M) :
    Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C) +
      ((Real.exp (-(1 / 10 : ℝ)) - 1) / 2) * M) ≤
    Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
      Real.exp (-(1 / 10 : ℝ) * C) * (Y / B) ^ tailSaving := by
  have hexp : Real.exp (-(1 / 10 : ℝ)) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  have hm := mul_le_mul_of_nonpos_left hM (show (Real.exp (-(1 / 10 : ℝ)) - 1) / 2 ≤ 0 by linarith)
  have hlog : Real.log (Y / B) = -Real.log (B / Y) := by
    rw [Real.log_div hY.ne' hB.ne', Real.log_div hB.ne' hY.ne']
    ring
  rw [Real.rpow_def_of_pos (div_pos hY hB), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  unfold tailSaving
  nlinarith

/-- The dyadic union bound is uniform in the number of endpoints and in C. -/
theorem dyadic_tail_chernoff_sum (S : Finset ℕ) {B Y K C : ℝ}
    (hB : 0 < B) (hY : 0 < Y) (M : ℕ → ℝ)
    (hM : ∀ i ∈ S, Real.log (B / ((2 : ℝ) ^ i * Y)) - K ≤ M i)
    (hcap : ∀ i ∈ S, (2 : ℝ) ^ i * Y ≤ B) :
    (∑ i ∈ S, Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / ((2 : ℝ) ^ i * Y)) - C) +
      ((Real.exp (-(1 / 10 : ℝ)) - 1) / 2) * M i)) ≤
      (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
        ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1))) * Real.exp (-(1 / 10 : ℝ) * C) := by
  calc
    _ ≤ ∑ i ∈ S, Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
        Real.exp (-(1 / 10 : ℝ) * C) * (((2 : ℝ) ^ i * Y) / B) ^ tailSaving :=
      sum_le_sum (fun i hi => tail_chernoff_factor_bound hB (by positivity) (hM i hi))
    _ = (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
        ∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ tailSaving := by rw [mul_sum]
    _ ≤ _ := by
      have h : (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
          (∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ tailSaving) ≤
          (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
          ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1)) :=
        mul_le_mul_of_nonneg_left (dyadic_power_sum_bound S hB hY.le tailSaving_pos hcap) (by positivity)
      convert h using 1 <;> first | rfl | ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularitySievePrimes
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of the sieve's actual prefix prime sets -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem good_prefix_sieve_set (P Z : ℕ) {U : ℝ} (hP : 6 ≤ P)
    (hU : 0 ≤ U) (hUZ : U ≤ Z) :
    (sievePrimes Z).filter (fun p => P < p ∧ p ∈ largePrimeSet U P) = largePrimeSet U P := by
  classical
  ext p
  constructor
  · intro hp
    exact (mem_filter.mp hp).2.2
  · intro hp
    obtain ⟨hpU, hpP⟩ := mem_filter.mp hp
    obtain ⟨hpU, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hpZ : p ≤ Z := by
      have hpr : (p : ℝ) ≤ U := (Nat.le_floor_iff hU).mp hpU
      exact_mod_cast hpr.trans hUZ
    have hPp : P < p := by exact_mod_cast hpP
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩, ⟨hPp, hp⟩⟩

theorem full_prefix_sieve_set (P Z : ℕ) {U : ℝ} (hP : 6 ≤ P) (hZU : (Z : ℝ) ≤ U) :
    (sievePrimes Z).filter (fun p => P < p ∧ p ∈ largePrimeSet U P) = largePrimeSet Z P := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpS, hpP, _⟩ := mem_filter.mp hp
    obtain ⟨hpZ, _⟩ := mem_filter.mp hpS
    apply mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simpa only [Nat.floor_natCast] using hpZ
    · exact_mod_cast hpP
  · intro hp
    obtain ⟨hpZ, hpP⟩ := mem_filter.mp hp
    rw [Nat.floor_natCast] at hpZ
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hPp : P < p := by exact_mod_cast hpP
    have hpU : p ≤ ⌊U⌋₊ := Nat.le_floor ((by exact_mod_cast hpZ : (p : ℝ) ≤ Z).trans hZU)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩,
      ⟨hPp, mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpU, hprime⟩, hpP⟩⟩⟩

theorem primePrefix_eq_largePrimeSet {B : ℕ} (hB : 1 ≤ B) {g : ℝ} (hg : g < 1) :
    primePrefix B g (auxiliaryPrimes B) =
      largePrimeSet (Real.exp ((B : ℝ) ^ g)) (auxiliaryCutoff B) := by
  classical
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpower : (B : ℝ) ^ g ≤ 4 * B := by
    have h := Real.rpow_le_rpow_of_exponent_le hB1 hg.le
    rw [Real.rpow_one] at h
    linarith
  have hupper : Real.exp ((B : ℝ) ^ g) ≤ auxiliaryUpper B := Real.exp_le_exp.mpr hpower
  rw [primePrefix, ite_eq_left hg]
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hplog⟩ := mem_filter.mp hp
    obtain ⟨hpU, hpCut⟩ := mem_filter.mp hpP
    obtain ⟨_, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpX : (p : ℝ) ≤ Real.exp ((B : ℝ) ^ g) := by
      simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hplog
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpX, hprime⟩, hpCut⟩
  · intro hp
    obtain ⟨hpU, hpCut⟩ := mem_filter.mp hp
    obtain ⟨hpU, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpX : (p : ℝ) ≤ Real.exp ((B : ℝ) ^ g) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mp hpU
    have hpUpper : p ≤ ⌊auxiliaryUpper B⌋₊ := Nat.le_floor (hpX.trans hupper)
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpUpper, hprime⟩, hpCut⟩, ?_⟩
    simpa only [Real.log_exp] using Real.log_le_log hp0 hpX

theorem prefix_endpoint_le_sieveCutoff {c g : ℝ} (hc : 0 < c) (hg : g < 1) :
    ∀ᶠ B : ℕ in atTop, Real.exp ((B : ℝ) ^ g) ≤ sieveCutoff c B := by
  have hlim : Tendsto (fun B : ℕ => (B : ℝ) ^ g / B) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (power_div_power_tendsto_zero hg).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds (by linarith : (0 : ℝ) < c / 2)),
    sieveCutoff_eventually hc, eventually_gt_atTop 0] with B hsmall hcut hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ g ≤ Real.log (sieveCutoff c B) := by
    have h := (div_le_iff₀ hB0).mp hsmall
    exact h.trans hcut.2.2.1
  have hZ : (0 : ℝ) < sieveCutoff c B := by exact_mod_cast (by omega : 0 < sieveCutoff c B)
  simpa only [Real.exp_log hZ] using Real.exp_le_exp.mpr hpow

/-- This is the actual reciprocal mass appearing in the tilted sieve,
including its finite cutoff, for every fixed regularity-grid point. -/
theorem tilt_prefix_mass_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c g : ℝ}
    (hc : 0 < c) (hc4 : c ≤ 4) (hg : 0 < g) (hg1 : g ≤ 1) :
    Tendsto (fun B : ℕ =>
      tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
        (primePrefix B g (auxiliaryPrimes B)) / auxiliaryLogLength B) atTop (𝓝 g) := by
  by_cases hglt : g < 1
  · have h := regularity_prefix_prime_sum_tendsto hM (by norm_num : (0 : ℝ) < 1) hg
    apply h.congr'
    filter_upwards [prefix_endpoint_le_sieveCutoff hc hglt,
      auxiliaryCutoff_tendsto.eventually_ge_atTop 6, eventually_ge_atTop 1] with B hX hP hB
    rw [one_mul, primePrefix_eq_largePrimeSet hB hglt]
    unfold tiltPrimeReciprocalMass
    rw [good_prefix_sieve_set _ _ hP (Real.exp_pos _).le hX]
  · have hg_eq : g = 1 := le_antisymm hg1 (le_of_not_gt hglt)
    subst g
    have h := regularity_prefix_prime_sum_tendsto hM hc (by norm_num : (0 : ℝ) < 1)
    apply h.congr'
    filter_upwards [sieveCutoff_eventually hc, auxiliaryCutoff_tendsto.eventually_ge_atTop 6] with B hcut hP
    have hZU : (sieveCutoff c B : ℝ) ≤ auxiliaryUpper B := by
      refine hcut.2.2.2.trans (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_right hc4 (Nat.cast_nonneg B)
    simp only [Real.rpow_one, primePrefix, lt_self_iff_false, ite_false, if_false]
    unfold tiltPrimeReciprocalMass auxiliaryPrimes
    rw [full_prefix_sieve_set _ _ hP hZU]
    simp only [largePrimeSet, Nat.floor_natCast, sieveCutoff]

open Classical in
theorem tail_sieve_set (B Z : ℕ) {Y : ℝ} (hP : 6 ≤ auxiliaryCutoff B)
    (hZU : (Z : ℝ) ≤ auxiliaryUpper B) (hY : Real.log (auxiliaryCutoff B) ≤ Y) :
    (sievePrimes Z).filter (fun p => auxiliaryCutoff B < p ∧
      p ∈ (auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) =
        largePrimeSet Z (Real.exp Y) := by
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by exact_mod_cast (by omega : 0 < auxiliaryCutoff B)
  have hPY : (auxiliaryCutoff B : ℝ) ≤ Real.exp Y := by
    simpa only [Real.exp_log hP0] using Real.exp_le_exp.mpr hY
  ext p
  constructor
  · intro hp
    obtain ⟨hpS, _hpP, hpQ⟩ := mem_filter.mp hp
    obtain ⟨hpZ, _⟩ := mem_filter.mp hpS
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hYp := (mem_filter.mp hpQ).2
    have hxp : Real.exp Y < (p : ℝ) := by
      simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hYp
    exact mem_filter.mpr ⟨by simpa only [Nat.floor_natCast] using Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, hxp⟩
  · intro hp
    obtain ⟨hpZ, hxp⟩ := mem_filter.mp hp
    rw [Nat.floor_natCast] at hpZ
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpP : auxiliaryCutoff B < p := by exact_mod_cast (hPY.trans_lt hxp)
    have hpU : p ≤ ⌊auxiliaryUpper B⌋₊ := Nat.le_floor ((by exact_mod_cast hpZ : (p : ℝ) ≤ Z).trans hZU)
    have hlog : Y < Real.log p := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos Y) hxp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩,
      hpP, mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpU, hprime⟩, by exact_mod_cast hpP⟩, hlog⟩⟩

theorem tilt_tail_mass_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ, Real.log (auxiliaryCutoff B) ≤ Y →
      Real.log ((B : ℝ) / Y) - K ≤ tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
        ((auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) := by
  classical
  obtain ⟨K, hK, hbound⟩ := regularity_tail_prime_sum_lower hM (by linarith : 0 < c / 2)
  refine ⟨K, hK, ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [sieveCutoff_eventually hc, auxiliaryCutoff_tendsto.eventually_ge_atTop 6,
    hloglarge, eventually_gt_atTop 0] with B hcut hP hlog hB
  intro Y hY
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hZU : (sieveCutoff c B : ℝ) ≤ auxiliaryUpper B :=
    hcut.2.2.2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc4 hB0.le))
  unfold tiltPrimeReciprocalMass
  rw [tail_sieve_set B _ hP hZU hY]
  exact hbound B (sieveCutoff c B) Y hB0 (by exact_mod_cast hcut.1) hcut.2.2.1 (hlog.trans hY)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularityChernoffFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chernoff factors with the actual truncated sieve prime sets -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem actual_prefix_chernoff_decay
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ c g : ℝ, 0 < c → c ≤ 4 → 0 < g → g ≤ 1 →
        Tendsto (fun B => prefixUpperFactor B c g τ s) atTop (𝓝 0) ∧
        Tendsto (fun B => prefixLowerFactor B c g τ s) atTop (𝓝 0) := by
  obtain ⟨s, hs, _hsτ, hs1, he, hen, hmargin⟩ := exists_prefix_tilt hτ
  refine ⟨s, hs, hs1, he, hen, ?_⟩
  intro c g hc hc4 hg hg1
  let m := fun B => tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B) (primePrefix B g (auxiliaryPrimes B))
  have hm : Tendsto (fun B => m B / auxiliaryLogLength B) atTop (𝓝 g) :=
    tilt_prefix_mass_tendsto hM hc hc4 hg hg1
  have hpos : -s * (g / 2 + τ) + ((Real.exp s - 1) / 2) * g < 0 := by
    have h := (hmargin g hg.le hg1).1
    nlinarith [mul_pos hs hτ]
  have hneg : s * (g / 2 - τ) + ((Real.exp (-s) - 1) / 2) * g < 0 := by
    have h := (hmargin g hg.le hg1).2
    nlinarith [mul_pos hs hτ]
  have hℓ : ∀ᶠ B : ℕ in atTop, auxiliaryLogLength B ≠ 0 :=
    (auxiliaryLogLength_tendsto.eventually_gt_atTop 0).mono (fun _ h => ne_of_gt h)
  constructor
  · have hlim := (hm.const_mul ((Real.exp s - 1) / 2)).const_add (-s * (g / 2 + τ))
    have hprod := hlim.neg_mul_atTop hpos auxiliaryLogLength_tendsto
    apply Real.tendsto_exp_atBot.comp (hprod.congr' ?_)
    filter_upwards [hℓ] with B hB
    dsimp [prefixUpperFactor, m]
    field_simp
  · have hlim := (hm.const_mul ((Real.exp (-s) - 1) / 2)).const_add (s * (g / 2 - τ))
    have hprod := hlim.neg_mul_atTop hneg auxiliaryLogLength_tendsto
    apply Real.tendsto_exp_atBot.comp (hprod.congr' ?_)
    filter_upwards [hℓ] with B hB
    dsimp [prefixLowerFactor, m]
    field_simp

theorem actual_tail_chernoff_sum
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 4) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ B : ℕ in atTop, ∀ (S : Finset ℕ) (C : ℝ),
      (∀ i ∈ S, primeTailEndpoint B i ≤ B) →
      (∑ i ∈ S, tailChernoffFactor B i c C) ≤ D * Real.exp (-(1 / 10 : ℝ) * C) := by
  classical
  obtain ⟨K, _hK, hbound⟩ := tilt_tail_mass_lower hM hc hc4
  let D := Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
    ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1))
  have hr : 1 < (2 : ℝ) ^ tailSaving := Real.one_lt_rpow (by norm_num) tailSaving_pos
  refine ⟨D, mul_pos (Real.exp_pos _) (div_pos (by positivity) (by linarith)), ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [hbound, hloglarge, eventually_gt_atTop 0] with B hB hlog hBpos
  intro S C hS
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hY0 : 0 < Real.log (auxiliaryCutoff B) := by linarith
  have hY (i : ℕ) : Real.log (auxiliaryCutoff B) ≤ primeTailEndpoint B i := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    exact le_mul_of_one_le_left hY0.le hp
  exact dyadic_tail_chernoff_sum S hB0 hY0
    (fun i => tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
      ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)))
    (fun i _ => hB (primeTailEndpoint B i) (hY i)) hS

theorem tail_endpoint_index_lt {B i : ℕ} (hlog : 1 ≤ Real.log (auxiliaryCutoff B))
    (hi : primeTailEndpoint B i < B) : i < B := by
  have hp : (i : ℝ) < (2 : ℝ) ^ i := by exact_mod_cast (show i < 2 ^ i from Nat.lt_two_pow_self)
  have hm : (2 : ℝ) ^ i ≤ primeTailEndpoint B i :=
    le_mul_of_one_le_right (by positivity) hlog
  exact_mod_cast hp.trans (hm.trans_lt hi)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularityUnionBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite union bound for every failure of the regularity cutoff -/

namespace JointDickman

open Finset

theorem prefixViolationMass_nonneg (B L : ℕ) (τ : ℝ) (S : Finset ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ prefixViolationMass B L τ S w := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs <;> linarith

theorem tailViolationMass_nonneg (B : ℕ) (C : ℝ) (S : Finset ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ tailViolationMass B C S w := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs <;> linarith

theorem regularity_failure_union_bound {B L : ℕ} {τ C w : ℝ} (S : Finset ℕ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) (hw : 0 ≤ w)
    (hbad : ¬RegularPrimeSet B L τ C S) :
    w ≤ prefixViolationMass B L τ S w + tailViolationMass B C S w := by
  classical
  have hpnon := prefixViolationMass_nonneg B L τ S hw
  have htnon := tailViolationMass_nonneg B C S hw
  unfold RegularPrimeSet at hbad
  rcases not_and_or.mp hbad with hprefix | htail
  · obtain ⟨i, hi⟩ := not_forall.mp hprefix
    obtain ⟨hi, hbad_i⟩ := Classical.not_imp.mp hi
    have hsingle :
        (if ((primePrefix B ((i : ℝ) / L) S).card : ℝ) <
            (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then w else 0) +
        (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
            ((primePrefix B ((i : ℝ) / L) S).card : ℝ) then w else 0) ≤ prefixViolationMass B L τ S w := by
      apply single_le_sum (fun j _ => ?_) hi
      split_ifs <;> linarith
    rcases not_and_or.mp hbad_i with hlo | hhi
    · rw [ite_eq_left (lt_of_not_ge hlo)] at hsingle
      split_ifs at hsingle <;> linarith
    · rw [ite_eq_left (lt_of_not_ge hhi)] at hsingle
      split_ifs at hsingle <;> linarith
  · obtain ⟨i, hi⟩ := not_forall.mp htail
    have hfail := lt_of_not_ge hi
    have hY : 0 < primeTailEndpoint B i := by
      unfold primeTailEndpoint
      positivity
    have hcount : (0 : ℝ) ≤ (S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card :=
      Nat.cast_nonneg _
    have hYi : primeTailEndpoint B i < B := by
      by_contra h
      have hBY : (B : ℝ) ≤ primeTailEndpoint B i := le_of_not_gt h
      have hdiv : (B : ℝ) / primeTailEndpoint B i ≤ 1 := (div_le_one hY).mpr hBY
      have hlog' := Real.log_nonpos (div_nonneg (Nat.cast_nonneg B) hY.le) hdiv
      linarith
    have hiB : i ∈ range B := mem_range.mpr (tail_endpoint_index_lt hlog hYi)
    have hsingle :
        (if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
            (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then w else 0) ≤
          tailViolationMass B C S w := by
      apply single_le_sum (fun j _ => ?_) hiB
      split_ifs <;> linarith
    rw [ite_eq_left hfail] at hsingle
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PrefixViolationSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual prefix failures on a fixed grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem prefixGridError_nonneg (B L : ℕ) (c τ s : ℝ) :
    0 ≤ prefixGridError B L c τ s := by
  apply sum_nonneg
  intro i _
  exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem prefixGridError_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ (L : ℕ) (c : ℝ), 0 < L → 0 < c → c ≤ 4 →
        Tendsto (fun B => prefixGridError B L c τ s) atTop (𝓝 0) := by
  obtain ⟨s, hs, hs1, he, hen, hdec⟩ := actual_prefix_chernoff_decay hM hτ
  refine ⟨s, hs, hs1, he, hen, ?_⟩
  intro L c hL hc hc4
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlim := tendsto_finsetSum (Icc 1 L) (f := fun (i : ℕ) B =>
    prefixLowerFactor B c ((i : ℝ) / L) τ s +
      prefixUpperFactor B c ((i : ℝ) / L) τ s) (a := fun _ => (0 : ℝ)) (fun i hi => by
        have hi' := mem_Icc.mp hi
        have hip : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
        have hil : (i : ℝ) ≤ L := by exact_mod_cast hi'.2
        have hh := hdec c ((i : ℝ) / L) hc hc4 (div_pos hip hL')
          ((div_le_one hL').mpr hil)
        simpa using hh.2.add hh.1)
  simpa only [prefixGridError, sum_const_zero] using hlim

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TailViolationSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic summation of the actual tail failures -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem tailViolationMass_eq_restricted {B : ℕ} {C : ℝ} (S : Finset ℕ) (w : ℝ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) :
    tailViolationMass B C S w = ∑ i ∈ activeTailIndices B,
      if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then w else 0 := by
  classical
  unfold tailViolationMass activeTailIndices
  rw [sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hi : primeTailEndpoint B i < B
  · simp only [hi, ite_true, if_true]
  · have hY : 0 < primeTailEndpoint B i := by unfold primeTailEndpoint; positivity
    have hdiv : (B : ℝ) / primeTailEndpoint B i ≤ 1 := (div_le_one hY).mpr (le_of_not_gt hi)
    have hlog' := Real.log_nonpos (div_nonneg (Nat.cast_nonneg B) hY.le) hdiv
    have hcount : (0 : ℝ) ≤ (S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card :=
      Nat.cast_nonneg _
    have hnot : ¬((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C := by linarith
    simp only [hi, hnot, ite_false, if_false]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeCountChernoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential bounds for counts in a selected prime subset -/

namespace JointDickman

open Finset

/-- The exact generating function for the count in Q. -/
theorem bernoulliSubsetMass_restricted_count_exp (P Q : Finset ℕ) (q : ℕ → ℝ) (s : ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card)) =
      ∏ p ∈ P ∩ Q, (1 - q p + q p * Real.exp s) := by
  classical
  have hv (S : Finset ℕ) : (∏ p ∈ S, if p ∈ Q then Real.exp s else 1) =
      Real.exp (s * (S ∩ Q).card) := by
    rw [← prod_filter, prod_const, ← Real.exp_nat_mul]
    have hf : S.filter (fun p => p ∈ Q) = S ∩ Q := by ext p; simp
    rw [hf]
    congr 1
    ring
  have h := bernoulliSubsetMass_tilt P q (fun p => if p ∈ Q then Real.exp s else 1)
  simp_rw [hv] at h
  rw [h]
  have heq (p : ℕ) : 1 - q p + q p * (if p ∈ Q then Real.exp s else 1) =
      if p ∈ Q then 1 - q p + q p * Real.exp s else 1 := by
    by_cases hp : p ∈ Q <;> simp [hp]
  simp_rw [heq]
  rw [← prod_filter]
  congr 1

theorem bernoulliSubsetMass_restricted_count_exp_bound (P Q : Finset ℕ)
    (q : ℕ → ℝ) (s : ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card)) ≤
      Real.exp ((Real.exp s - 1) * ∑ p ∈ P ∩ Q, q p) := by
  rw [bernoulliSubsetMass_restricted_count_exp]
  calc
    _ ≤ ∏ p ∈ P ∩ Q, Real.exp ((Real.exp s - 1) * q p) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpP := (mem_inter.mp hp).1
        exact add_nonneg (sub_nonneg.mpr (hq p hpP).2)
          (mul_nonneg (hq p hpP).1 (Real.exp_pos _).le)
      · intro p _
        have h := Real.add_one_le_exp ((Real.exp s - 1) * q p)
        nlinarith
    _ = _ := by rw [← Real.exp_sum, ← mul_sum]

/-- Both upper and lower tails are covered by the signed threshold
`s*r ≤ s*count`; no asymptotic or distributional premise is hidden here. -/
theorem bernoulliSubsetMass_restricted_count_tail (P Q : Finset ℕ)
    (q : ℕ → ℝ) (s r : ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, if s * r ≤ s * (S ∩ Q).card then bernoulliSubsetMass P q S else 0) ≤
      Real.exp (-s * r + (Real.exp s - 1) * ∑ p ∈ P ∩ Q, q p) := by
  classical
  have hmark : Real.exp (s * r) *
      (∑ S ∈ P.powerset, if s * r ≤ s * (S ∩ Q).card then bernoulliSubsetMass P q S else 0) ≤
        ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card) := by
    rw [mul_sum]
    apply sum_le_sum
    intro S hS
    have hmass := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    split_ifs with h
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) hmass
    · simpa only [mul_zero] using mul_nonneg hmass (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left
    (hmark.trans (bernoulliSubsetMass_restricted_count_exp_bound P Q q s hq)) (Real.exp_pos (-s * r)).le
  have he : Real.exp (-s * r) * Real.exp (s * r) = 1 := by
    rw [← Real.exp_add]
    rw [show -s * r + s * r = 0 by ring, Real.exp_zero]
  simpa only [← mul_assoc, he, one_mul, ← Real.exp_add] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIndicatorErrors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stable prime-count estimates for the conditional indicator parameters -/

namespace JointDickman

open Finset

/-- Absolute errors in the inclusion probabilities control every restricted mean. -/
theorem restricted_indicator_mean_error (P Q : Finset ℕ) (q : ℕ → ℝ) {D : ℝ}
    (hD : (∑ p ∈ P, |q p - (1 / 2 : ℝ) / p|) ≤ D) :
    |(∑ p ∈ P ∩ Q, q p) - (1 / 2 : ℝ) * (∑ p ∈ P ∩ Q, 1 / (p : ℝ))| ≤ D := by
  calc
    _ = |∑ p ∈ P ∩ Q, (q p - (1 / 2 : ℝ) / p)| := by
      congr 1
      rw [sum_sub_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ P ∩ Q, |q p - (1 / 2 : ℝ) / p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, |q p - (1 / 2 : ℝ) / p| :=
      sum_le_sum_of_subset_of_nonneg inter_subset_left (fun _ _ _ => abs_nonneg _)
    _ ≤ D := hD

/-- A bounded total parameter error changes either signed exponential factor
by at most exp D, uniformly for exp s <= 2. -/
theorem exponential_mean_error {m M s r D : ℝ} (_hD : 0 ≤ D)
    (hmean : |m - M / 2| ≤ D) (hs : Real.exp s ≤ 2) :
    Real.exp (-s * r + (Real.exp s - 1) * m) ≤
      Real.exp D * Real.exp (-s * r + ((Real.exp s - 1) / 2) * M) := by
  have habs : |Real.exp s - 1| ≤ 1 := abs_le.mpr ⟨by linarith [Real.exp_pos s], by linarith⟩
  have hprod : |(Real.exp s - 1) * (m - M / 2)| ≤ D := by
    rw [abs_mul]
    exact (mul_le_mul habs hmean (abs_nonneg _) (by norm_num)).trans_eq (one_mul D)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hu := (abs_le.mp hprod).2
  nlinarith only [hu]

/-- At the full cutoff the sieve mass is just the actual prime reciprocal
mass, so the same Chernoff factors bound the indicator probabilities. -/
theorem full_cutoff_prime_mass (B : ℕ) (Q : Finset ℕ)
    (hP : 6 ≤ auxiliaryCutoff B) :
    tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q =
      ∑ p ∈ auxiliaryPrimes B ∩ Q, 1 / (p : ℝ) := by
  classical
  have hset : (sievePrimes (sieveCutoff 4 B)).filter
      (fun p => auxiliaryCutoff B < p ∧ p ∈ Q) = auxiliaryPrimes B ∩ Q := by
    ext p
    simp only [mem_filter, mem_inter, sievePrimes, auxiliaryPrimes, auxiliaryUpper,
      sieveCutoff, largePrimeSet, mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hpZ, hp⟩, _hp6⟩, hpP, hpQ⟩
      exact ⟨⟨⟨hpZ, hp⟩, by exact_mod_cast hpP⟩, hpQ⟩
    · rintro ⟨⟨⟨hpZ, hp⟩, hpP⟩, hpQ⟩
      have hPp : auxiliaryCutoff B < p := by exact_mod_cast hpP
      exact ⟨⟨⟨hpZ, hp⟩, by omega⟩, hPp, hpQ⟩
  unfold tiltPrimeReciprocalMass
  rw [hset]

theorem bernoulli_count_tail_stable (B : ℕ) (Q : Finset ℕ) (q : ℕ → ℝ)
    (s r : ℝ) {D : ℝ} (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : Real.exp s ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if s * r ≤ s * (S ∩ Q).card then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * Real.exp (-s * r + ((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q) := by
  have hmean := restricted_indicator_mean_error (auxiliaryPrimes B) Q q herr
  rw [← full_cutoff_prime_mass B Q hP] at hmean
  have hmean' : |(∑ p ∈ auxiliaryPrimes B ∩ Q, q p) -
      tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q / 2| ≤ D := by
    convert hmean using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  exact (bernoulliSubsetMass_restricted_count_tail _ Q q s r hq).trans
    (exponential_mean_error hD hmean' hs)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIndicatorViolations
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prefix and tail violation probabilities -/

namespace JointDickman

open Finset

private theorem primePrefix_of_subset {S P : Finset ℕ} (hS : S ⊆ P) (B : ℕ) (g : ℝ) :
    primePrefix B g S = S ∩ primePrefix B g P := by
  simpa only [inter_eq_left.mpr hS] using primePrefix_inter B g S P

private theorem primeTail_of_subset {S P : Finset ℕ} (hS : S ⊆ P) (Y : ℝ) :
    S.filter (fun p : ℕ => Y < Real.log p) = S ∩ P.filter (fun p : ℕ => Y < Real.log p) := by
  ext p
  simp only [mem_filter, mem_inter]
  exact ⟨fun h => ⟨h.1, hS h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

theorem bernoulli_strict_lower_tail (B : ℕ) (Q : Finset ℕ) (q : ℕ → ℝ)
    (s r : ℝ) {D : ℝ} (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp (-s) ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S ∩ Q).card : ℝ) < r then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * Real.exp (s * r + ((Real.exp (-s) - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q) := by
  classical
  have hb := bernoulli_count_tail_stable B Q q (-s) r hP hD hq herr he
  have hc : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S ∩ Q).card : ℝ) < r then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      ∑ S ∈ (auxiliaryPrimes B).powerset,
        if -s * r ≤ -s * (S ∩ Q).card then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0 := by
    apply sum_le_sum
    intro S hS
    have hw := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    split_ifs with h h' h'
    · exact le_rfl
    · exfalso
      exact h' (by nlinarith only [h, hs])
    · exact hw
    · exact le_rfl
  simpa only [neg_neg] using hc.trans hb

theorem bernoulli_strict_upper_tail (B : ℕ) (Q : Finset ℕ) (q : ℕ → ℝ)
    (s r : ℝ) {D : ℝ} (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp s ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if r < ((S ∩ Q).card : ℝ) then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * Real.exp (-s * r + ((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q) := by
  classical
  apply LE.le.trans _ (bernoulli_count_tail_stable B Q q s r hP hD hq herr he)
  apply sum_le_sum
  intro S hS
  have hw := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
  split_ifs with h h' h'
  · exact le_rfl
  · exfalso
    exact h' (by nlinarith only [h, hs])
  · exact hw
  · exact le_rfl

theorem bernoulli_prefix_lower_bound (B : ℕ) (q : ℕ → ℝ) (g τ s : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp (-s) ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((primePrefix B g S).card : ℝ) < (g / 2 - τ) * auxiliaryLogLength B
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * prefixLowerFactor B 4 g τ s := by
  classical
  have hb := bernoulli_strict_lower_tail B (primePrefix B g (auxiliaryPrimes B)) q
    s ((g / 2 - τ) * auxiliaryLogLength B) hP hD hq herr hs he
  have heq : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((primePrefix B g S).card : ℝ) < (g / 2 - τ) * auxiliaryLogLength B
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S ∩ primePrefix B g (auxiliaryPrimes B)).card : ℝ) < (g / 2 - τ) * auxiliaryLogLength B
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0 := by
    apply sum_congr rfl
    intro S hS
    rw [primePrefix_of_subset (mem_powerset.mp hS)]
  rw [heq]
  simpa only [prefixLowerFactor, mul_assoc] using hb

theorem bernoulli_prefix_upper_bound (B : ℕ) (q : ℕ → ℝ) (g τ s : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp s ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if (g / 2 + τ) * auxiliaryLogLength B < ((primePrefix B g S).card : ℝ)
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * prefixUpperFactor B 4 g τ s := by
  classical
  have hb := bernoulli_strict_upper_tail B (primePrefix B g (auxiliaryPrimes B)) q
    s ((g / 2 + τ) * auxiliaryLogLength B) hP hD hq herr hs he
  have heq : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if (g / 2 + τ) * auxiliaryLogLength B < ((primePrefix B g S).card : ℝ)
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset,
      if (g / 2 + τ) * auxiliaryLogLength B < ((S ∩ primePrefix B g (auxiliaryPrimes B)).card : ℝ)
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0 := by
    apply sum_congr rfl
    intro S hS
    rw [primePrefix_of_subset (mem_powerset.mp hS)]
  rw [heq]
  simpa only [prefixUpperFactor, mul_assoc] using hb

theorem bernoulli_tail_violation_bound (B i : ℕ) (q : ℕ → ℝ) (C : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * tailChernoffFactor B i 4 C := by
  classical
  have he : Real.exp (-(1 / 10 : ℝ)) ≤ 2 :=
    (Real.exp_le_exp.mpr (by norm_num : -(1 / 10 : ℝ) ≤ 0)).trans (by norm_num)
  have hb := bernoulli_strict_lower_tail B
    ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) q
    (1 / 10) ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C)
    hP hD hq herr (by norm_num) he
  have heq : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S ∩ (auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0 := by
    apply sum_congr rfl
    intro S hS
    rw [primeTail_of_subset (mem_powerset.mp hS)]
  rw [heq]
  exact hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIndicatorRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform regularity loss for independent prime indicators -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem bernoulli_prefix_violation_sum (B L : ℕ) (q : ℕ → ℝ) (τ s : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp s ≤ 2) (hen : Real.exp (-s) ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      prefixViolationMass B L τ S (bernoulliSubsetMass (auxiliaryPrimes B) q S)) ≤
        Real.exp D * prefixGridError B L 4 τ s := by
  classical
  unfold prefixViolationMass
  rw [sum_comm]
  unfold prefixGridError
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  simp only [sum_add_distrib, mul_add]
  exact add_le_add (bernoulli_prefix_lower_bound B q ((i : ℝ) / L) τ s hP hD hq herr hs hen)
    (bernoulli_prefix_upper_bound B q ((i : ℝ) / L) τ s hP hD hq herr hs he)

theorem bernoulli_tail_violation_sum (B : ℕ) (q : ℕ → ℝ) (C : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) (hC : 0 ≤ C)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      tailViolationMass B C S (bernoulliSubsetMass (auxiliaryPrimes B) q S)) ≤
        Real.exp D * (∑ i ∈ activeTailIndices B, tailChernoffFactor B i 4 C) := by
  classical
  simp_rw [tailViolationMass_eq_restricted _ _ hC hlog]
  rw [sum_comm, mul_sum]
  exact sum_le_sum (fun i _ => bernoulli_tail_violation_bound B i q C hP hD hq herr)

theorem bernoulli_regularity_failure_bound (B L : ℕ) (q : ℕ → ℝ) (τ s C : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) (hC : 0 ≤ C)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp s ≤ 2) (hen : Real.exp (-s) ≤ 2) :
    primeRegularityFailureProbability B L τ C q ≤
      Real.exp D * (prefixGridError B L 4 τ s +
        ∑ i ∈ activeTailIndices B, tailChernoffFactor B i 4 C) := by
  classical
  have hpoint : primeRegularityFailureProbability B L τ C q ≤
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        prefixViolationMass B L τ S (bernoulliSubsetMass (auxiliaryPrimes B) q S)) +
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        tailViolationMass B C S (bernoulliSubsetMass (auxiliaryPrimes B) q S)) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro S hS
    have hw := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    split_ifs with hreg
    · exact add_nonneg (prefixViolationMass_nonneg B L τ S hw) (tailViolationMass_nonneg B C S hw)
    · exact regularity_failure_union_bound S hC hlog hw hreg
  have hp := bernoulli_prefix_violation_sum B L q τ s hP hD hq herr hs he hen
  have ht := bernoulli_tail_violation_sum B q C hP hD hlog hC hq herr
  simpa only [mul_add] using hpoint.trans (add_le_add hp ht)

/-- The probability version of manuscript (9), uniform over all proper
independent parameters with bounded total deviation from 1/(2p). -/
theorem independent_prime_regularity_loss
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (q : ℕ → ℝ) (C : ℝ), 0 ≤ C →
          (∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1) →
          (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D →
          primeRegularityFailureProbability B L τ C q ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨Dt, hDt, htail⟩ := actual_tail_chernoff_sum hM (by norm_num : (0 : ℝ) < 4) (by norm_num)
  let K := Real.exp D * (Dt + 1)
  refine ⟨K, mul_pos (Real.exp_pos _) (by linarith only [hDt]), ?_⟩
  intro L τ hL hτ
  obtain ⟨s, hs, _hs1, he, hen, hprefix⟩ := prefixGridError_tendsto hM hτ
  refine ⟨fun B => prefixGridError B L 4 τ s, fun B => prefixGridError_nonneg ..,
    hprefix L 4 hL (by norm_num) (by norm_num), ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [htail, hloglarge, auxiliaryCutoff_tendsto.eventually_ge_atTop 6] with B ht hlog hP
  intro q C hC hq herr
  have hb := bernoulli_regularity_failure_bound B L q τ s C hP hD hlog hC hq herr hs he hen
  have ht' := ht (activeTailIndices B) C (fun i hi => (mem_filter.mp hi).2.le)
  have hbase := prefixGridError_nonneg B L 4 τ s
  have hexp := (Real.exp_pos (-(1 / 10 : ℝ) * C)).le
  calc
    _ ≤ Real.exp D * (prefixGridError B L 4 τ s + Dt * Real.exp (-(1 / 10 : ℝ) * C)) :=
      hb.trans (mul_le_mul_of_nonneg_left (add_le_add_right ht' _) (Real.exp_pos _).le)
    _ ≤ K * (prefixGridError B L 4 τ s + Real.exp (-(1 / 10 : ℝ) * C)) := by
      dsimp only [K]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos D).le
      nlinarith only [mul_nonneg hDt.le hbase, hexp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ConditionalPrimeParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual remaining-prime parameters after a coefficient is selected -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem remainingPrimeParameter_mem_Icc (S : Finset ℕ) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ remainingPrimeParameter S p ∧ remainingPrimeParameter S p ≤ 1 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold remainingPrimeParameter
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · refine ⟨div_nonneg (by norm_num) (by linarith), ?_⟩
    exact (div_le_one (by linarith : 0 < 2 * (p : ℝ) - 1)).mpr (by linarith)

theorem unselected_parameter_error {p : ℕ} (hp : 2 ≤ p) :
    |1 / (2 * (p : ℝ) - 1) - (1 / 2 : ℝ) / p| ≤ 1 / (p : ℝ)^2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < 2 * (p : ℝ) - 1 := by linarith
  have heq : 1 / (2 * (p : ℝ) - 1) - (1 / 2 : ℝ) / p =
      1 / (2 * (p : ℝ) * (2 * p - 1)) := by
    field_simp
    ring
  rw [heq, abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (p : ℝ)^2)
  nlinarith only [hp']

theorem remaining_parameter_total_error {P S : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    (∑ p ∈ P, |remainingPrimeParameter S p - (1 / 2 : ℝ) / p|) ≤
      1 + ∑ p ∈ S, 1 / (p : ℝ) := by
  classical
  have hpoint (p : ℕ) (hp : p ∈ P) :
      |remainingPrimeParameter S p - (1 / 2 : ℝ) / p| ≤
        1 / (p : ℝ)^2 + if p ∈ S then 1 / (p : ℝ) else 0 := by
    by_cases hs : p ∈ S
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      simp only [remainingPrimeParameter, hs, ite_true, if_true, zero_sub, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) / p)]
      have hh : (1 / 2 : ℝ) / p ≤ 1 / (p : ℝ) :=
        div_le_div_of_nonneg_right (by norm_num) hp0.le
      linarith [show (0 : ℝ) ≤ 1 / (p : ℝ)^2 by positivity]
    · simpa only [remainingPrimeParameter, hs, ite_false, if_false, add_zero] using
        unselected_parameter_error (hP p hp).two_le
  have hsum := sum_le_sum hpoint
  have heq : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hsq : (∑ p ∈ P, 1 / (p : ℝ)^2) ≤ 1 := by
    simpa using sum_reciprocal_square_tail P (by norm_num : (1 : ℕ) ≠ 0) (fun p hp => (hP p hp).one_lt)
  rw [sum_add_distrib, ← sum_filter, heq] at hsum
  exact hsum.trans (add_le_add_left hsq _)

/-- Omitting a coefficient of fixed exponential size costs o(1) in total
reciprocal prime mass, uniformly in the coefficient. -/
theorem auxiliary_selected_reciprocal_sum_small {κ : ℝ} (_hκ : 0 < κ) :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp (κ * B) → (∑ p ∈ S, 1 / (p : ℝ)) ≤ 1 := by
  have ht : Tendsto (fun B : ℕ => (κ / Real.log 2) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have hp := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (κ / Real.log 2)
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using hp
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp (hS hp)).1).2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ κ * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  calc
    _ ≤ ∑ _p ∈ S, 1 / (auxiliaryCutoff B : ℝ) := sum_le_sum (fun p hp =>
      one_div_le_one_div_of_le hP0 (mem_filter.mp (hS hp)).2.le)
    _ = (S.card : ℝ) / auxiliaryCutoff B := by simp [div_eq_mul_inv]
    _ ≤ (κ * B / Real.log 2) / auxiliaryCutoff B := div_le_div_of_nonneg_right hcard hP0.le
    _ = (κ / Real.log 2) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
    _ ≤ 1 := hsmall.le

/-- Uniform regularity of the remaining indicators after any selected
coefficient in the fixed exponential range. -/
theorem remaining_prime_regularity_loss
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ : ℝ} (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (S : Finset ℕ) (C : ℝ), 0 ≤ C → S ⊆ auxiliaryPrimes B →
          (∏ p ∈ S, p : ℕ) ≤ Real.exp (κ * B) →
          primeRegularityFailureProbability B L τ C (remainingPrimeParameter S) ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hbound⟩ := independent_prime_regularity_loss hM (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨K, hK, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε, hlim, hevent⟩ := hbound L τ hL hτ
  refine ⟨ε, hε, hlim, ?_⟩
  filter_upwards [hevent, auxiliary_selected_reciprocal_sum_small hκ] with B hB hsmall
  intro S C hC hS hn
  have hprime : ∀ p ∈ auxiliaryPrimes B, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  apply hB (remainingPrimeParameter S) C hC
  · exact fun p hp => remainingPrimeParameter_mem_Icc S (hprime p hp).two_le
  · exact (remaining_parameter_total_error hprime hS).trans (by linarith only [hsmall S hS hn])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConditionalFairSplit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact conditional law of the remaining half of a prime site -/

namespace JointDickman

open Finset

private theorem subsetMass_prod_ite {P S : Finset ℕ} (hS : S ⊆ P) (q : ℕ → ℝ) :
    bernoulliSubsetMass P q S = ∏ p ∈ P, if p ∈ S then q p else 1 - q p := by
  classical
  rw [prod_ite]
  have hyes : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hno : P.filter (fun p => p ∉ S) = P \ S := by ext p; simp
  rw [hyes, hno]
  rfl

private theorem subsetMass_tilt_product {P S : Finset ℕ} (hS : S ⊆ P) (q v : ℕ → ℝ) :
    bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, if p ∈ S then q p * v p else 1 - q p := by
  classical
  rw [prod_ite]
  have hyes : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hno : P.filter (fun p => p ∉ S) = P \ S := by ext p; simp
  rw [hyes, hno, prod_mul_distrib]
  unfold bernoulliSubsetMass
  ring

/-- The exact joint mass factors into the selected marginal and the
independent remaining indicators, including the zero probabilities at A. -/
theorem fairSelectedRemainingMass_factor {P A R : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (hR : R ⊆ P) :
    fairSelectedRemainingMass P A R =
      bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
      bernoulliSubsetMass P (remainingPrimeParameter A) R := by
  classical
  by_cases hd : Disjoint A R
  · rw [fairSelectedRemainingMass, ite_eq_left hd,
      show (1 / 2 : ℝ)^(A ∪ R).card = ∏ _p ∈ A ∪ R, (1 / 2 : ℝ) by simp,
      subsetMass_tilt_product (union_subset hA hR), subsetMass_prod_ite hA,
      subsetMass_prod_ite hR, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hden : 2 * (p : ℝ) - 1 ≠ 0 := by linarith only [hp2]
    have hden' : -1 + (p : ℝ) * 2 ≠ 0 := by linarith only [hp2]
    by_cases ha : p ∈ A <;> by_cases hr : p ∈ R
    · exact False.elim ((disjoint_left.mp hd) ha hr)
    · simp only [mem_union, ha, hr, true_or, ite_true, if_true, ite_false, if_false, remainingPrimeParameter]
      ring
    · simp only [mem_union, ha, hr, false_or, ite_true, if_true, ite_false, if_false, remainingPrimeParameter]
      field_simp [hp0, hden, hden']
      linear_combination - (mul_inv_cancel₀ hden')
    · simp only [mem_union, ha, hr, false_or, ite_false, if_false, remainingPrimeParameter]
      field_simp [hp0, hden, hden']
      linear_combination mul_inv_cancel₀ hden'
  · rw [fairSelectedRemainingMass, ite_eq_right hd]
    obtain ⟨p, hpA, hpR⟩ := not_disjoint_iff.mp hd
    have hzero : bernoulliSubsetMass P (remainingPrimeParameter A) R = 0 := by
      unfold bernoulliSubsetMass
      have hz : (∏ p ∈ R, remainingPrimeParameter A p) = 0 := by
        apply prod_eq_zero hpR
        simp only [remainingPrimeParameter, hpA, ite_true, if_true]
      rw [hz, zero_mul]
    rw [hzero, mul_zero]

open Classical in
/-- Summing the exact joint split mass over nonregular remainders gives the
selected marginal times the failure probability proved above. -/
theorem fairSelectedRemainingMass_bad (B L : ℕ) (τ C : ℝ) {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    (∑ R ∈ (auxiliaryPrimes B).powerset,
      if RegularPrimeSet B L τ C R then 0 else fairSelectedRemainingMass (auxiliaryPrimes B) A R) =
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
        primeRegularityFailureProbability B L τ C (remainingPrimeParameter A) := by
  classical
  unfold primeRegularityFailureProbability
  rw [mul_sum]
  apply sum_congr rfl
  intro R hR
  have hP : ∀ p ∈ auxiliaryPrimes B, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  rw [fairSelectedRemainingMass_factor hP hA (mem_powerset.mp hR)]
  split_ifs <;> simp only [mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RemainingSplitRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity loss under the actual conditional fair-split law -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem fair_selected_remaining_regularity_loss
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ : ℝ} (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (A : Finset ℕ) (C : ℝ), 0 ≤ C → A ⊆ auxiliaryPrimes B →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
          (∑ R ∈ (auxiliaryPrimes B).powerset,
            if RegularPrimeSet B L τ C R then 0 else fairSelectedRemainingMass (auxiliaryPrimes B) A R) ≤
            bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
              K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hbound⟩ := remaining_prime_regularity_loss hM hκ
  refine ⟨K, hK, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε, hlim, hevent⟩ := hbound L τ hL hτ
  refine ⟨ε, hε, hlim, ?_⟩
  filter_upwards [hevent] with B hB
  intro A C hC hA hprod
  rw [fairSelectedRemainingMass_bad B L τ C hA, mul_assoc]
  apply mul_le_mul_of_nonneg_left (hB A C hC hA hprod)
  apply bernoulliSubsetMass_nonneg hA
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.two_le
  refine ⟨by positivity, ?_⟩
  exact (div_le_one (by linarith only [hp2] : (0 : ℝ) < p)).mpr (by linarith only [hp2])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FairSplitPairRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two remaining subsets in the amplification model -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem fairSelectedRemainingMass_nonneg {P A R : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (hR : R ⊆ P) :
    0 ≤ fairSelectedRemainingMass P A R := by
  unfold fairSelectedRemainingMass
  split_ifs
  · apply mul_nonneg _ (by positivity)
    apply bernoulliSubsetMass_nonneg (union_subset hA hR)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  · exact le_rfl

theorem fairSelectedRemainingMass_sum {P A : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) :
    (∑ R ∈ P.powerset, fairSelectedRemainingMass P A R) =
      bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A := by
  calc
    _ = ∑ R ∈ P.powerset,
        bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
          bernoulliSubsetMass P (remainingPrimeParameter A) R := by
      apply sum_congr rfl
      intro R hR
      exact fairSelectedRemainingMass_factor hP hA (mem_powerset.mp hR)
    _ = _ := by rw [← mul_sum, bernoulliSubsetMass_sum, mul_one]

open Classical in
theorem fairRemainingPairFailure_union (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    fairRemainingPairFailure B L τ C A D ≤
      (∑ R ∈ (auxiliaryPrimes B).powerset,
        if RegularPrimeSet B L τ C R then 0 else fairSelectedRemainingMass (auxiliaryPrimes B) A R) *
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D +
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
        (∑ Q ∈ (auxiliaryPrimes B).powerset,
          if RegularPrimeSet B L τ C Q then 0 else fairSelectedRemainingMass (auxiliaryPrimes B) D Q) := by
  classical
  have hP : ∀ p ∈ auxiliaryPrimes B, p.Prime := auxiliaryPrimes_prime B
  rw [← fairSelectedRemainingMass_sum hP hD, ← fairSelectedRemainingMass_sum hP hA,
    sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  unfold fairRemainingPairFailure
  apply sum_le_sum
  intro R hR
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro Q hQ
  have hx := fairSelectedRemainingMass_nonneg hP hA (mem_powerset.mp hR)
  have hy := fairSelectedRemainingMass_nonneg hP hD (mem_powerset.mp hQ)
  by_cases hr : RegularPrimeSet B L τ C R <;> by_cases hq : RegularPrimeSet B L τ C Q
  all_goals simp only [hr, hq, and_self, and_true, and_false, ite_true, if_true, ite_false, if_false,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals nlinarith only [mul_nonneg hx hy]

/-- Uniformly in the two selected coefficients, the two remaining subsets
lose at most the selected marginal mass times the regularity error. -/
theorem fair_remaining_pair_regularity_loss
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ : ℝ} (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (A D : Finset ℕ) (C : ℝ), 0 ≤ C →
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
          (∏ p ∈ D, p : ℕ) ≤ Real.exp (κ * B) →
          fairRemainingPairFailure B L τ C A D ≤
            (bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D) *
                K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hbound⟩ := fair_selected_remaining_regularity_loss hM hκ
  refine ⟨2 * K, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε0, hε, hevent⟩ := hbound L τ hL hτ
  refine ⟨ε, hε0, hε, ?_⟩
  filter_upwards [hevent] with B hb
  intro A D C hC hA hD ha hd
  have hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ (1 / 2 : ℝ) / p ∧ (1 / 2 : ℝ) / p ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  have hA0 := bernoulliSubsetMass_nonneg hA hq
  have hD0 := bernoulliSubsetMass_nonneg hD hq
  have ha' := mul_le_mul_of_nonneg_right (hb A C hC hA ha) hD0
  have hd' := mul_le_mul_of_nonneg_left (hb D C hC hD hd) hA0
  have hu := fairRemainingPairFailure_union B L τ C hA hD
  nlinarith only [hu, ha', hd']

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticSplitWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic coefficient weights on actual squarefree site divisors -/

namespace JointDickman
open Finset

theorem auxiliarySubset_disjoint_small {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : Disjoint A (Nat.primesLE (auxiliaryCutoff B)) := by
  apply disjoint_left.mpr
  intro p hp hsmall
  have hp0 : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp (hA hp)).2
  exact (not_lt_of_ge (Nat.mem_primesLE.mp hsmall).1) hp0

theorem coefficientPrimeSet_primeProduct {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : coefficientPrimeSet B (∏ p ∈ A, p) = A := by
  have hp : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  have hn : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)
  rw [coefficientPrimeSet_eq_inter hn, Nat.primeFactors_prod hp, inter_eq_left.mpr hA]

theorem coefficientWeight_primeProduct {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    coefficientWeight B (∏ p ∈ A, p) = Real.log (auxiliaryCutoff B) * residueBaseWeight B A := by
  have hp : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  simp only [coefficientWeight, coefficientScale, residueBaseWeight,
    roughSquarefreeWeight, ArithmeticFunction.coe_mk, Nat.primeFactors_prod hp,
    auxiliarySubset_disjoint_small hA, ite_true, if_true, squarefreeWeight,
    primeProduct_squarefree A hp, primeProduct_cardFactors A hp]
  ring

open Classical in
theorem regularCoefficientWeight_primeProduct {B L : ℕ} {τ C : ℝ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    regularCoefficientWeight B L τ C (∏ p ∈ A, p) =
      Real.log (auxiliaryCutoff B) * regularResidueWeight B L τ C A := by
  rw [regularCoefficientWeight, coefficientPrimeSet_primeProduct hA]
  by_cases hr : RegularPrimeSet B L τ C A <;>
    simp only [regularResidueWeight, hr, ite_true, if_true, ite_false, if_false, mul_zero]
  exact coefficientWeight_primeProduct hA

open Classical in
/-- On a squarefree site, the arithmetic divisor and quotient weights are
exactly B times the fair-retention mass with its two regularity indicators. -/
theorem regular_arithmetic_split_identity {B L : ℕ} {τ C : ℝ} {S A : Finset ℕ}
    (hB : 1 < B) (hS : S ⊆ auxiliaryPrimes B) (hA : A ⊆ S) :
    regularCoefficientWeight B L τ C (∏ p ∈ A, p) * regularResidueWeight B L τ C (S \ A) =
      (B : ℝ) * subsetRetentionMass S A *
        (if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A) then 1 else 0) := by
  rw [regularCoefficientWeight_primeProduct (hA.trans hS)]
  have he := fairSplit_weight_identity hA (Real.log (auxiliaryCutoff B)) (auxiliaryRatio B)
    (auxiliaryRatio_pos hB).le
  have he' : (Real.log (auxiliaryCutoff B) * residueBaseWeight B A) *
      residueBaseWeight B (S \ A) = (B : ℝ) * subsetRetentionMass S A := by
    unfold residueBaseWeight subsetRetentionMass
    rw [ite_eq_left hA, ← Real.sqrt_eq_rpow]
    calc
      _ = Real.log (auxiliaryCutoff B) * auxiliaryRatio B * (1 / 2 : ℝ)^S.card := by
        convert he using 1 <;> first | rfl | ring
      _ = _ := by rw [mul_comm (Real.log _) _, auxiliaryRatio_mul_log hB]
  by_cases ha : RegularPrimeSet B L τ C A <;>
    by_cases hr : RegularPrimeSet B L τ C (S \ A)
  all_goals simp only [regularResidueWeight, ha, hr, and_self, and_false, false_and,
    ite_true, if_true, ite_false, if_false, mul_zero, zero_mul, mul_one]
  exact he'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientProductSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero coefficients on the application range are auxiliary-prime products -/

namespace JointDickman
open Finset

open Classical in
theorem coefficientWeight_prime_support {B n : ℕ}
    (hn : coefficientWeight B n ≠ 0) (hsize : (n : ℝ) ≤ auxiliaryUpper B) :
    Squarefree n ∧ n.primeFactors ⊆ auxiliaryPrimes B := by
  have hrough : Disjoint n.primeFactors (Nat.primesLE (auxiliaryCutoff B)) := by
    by_contra hd
    exact hn (by simp [coefficientWeight,roughSquarefreeWeight,hd])
  have hsq : Squarefree n := by
    by_contra hs
    exact hn (by simp [coefficientWeight,roughSquarefreeWeight,squarefreeWeight,hs])
  refine ⟨hsq,?_⟩
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hpn := Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) (Nat.mem_primeFactors.mp hp).2.1
  have hlarge : auxiliaryCutoff B < p := by
    by_contra h
    exact disjoint_left.mp hrough hp (Nat.mem_primesLE.mpr ⟨by omega,hprime⟩)
  change p ∈ largePrimeSet (auxiliaryUpper B) (auxiliaryCutoff B)
  apply mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,?_⟩
  · exact (Nat.le_floor_iff (le_trans (Nat.cast_nonneg n) hsize)).mpr
      ((by exact_mod_cast hpn : (p : ℝ) ≤ n).trans hsize)
  · exact_mod_cast hlarge

open Classical in
theorem coefficientWeight_eq_primeProduct {B n : ℕ}
    (hn : coefficientWeight B n ≠ 0) (hsize : (n : ℝ) ≤ auxiliaryUpper B) :
    n = ∏ p ∈ coefficientPrimeSet B n,p := by
  obtain ⟨hsq,hsub⟩ := coefficientWeight_prime_support hn hsize
  rw [coefficientPrimeSet_eq_inter hsq.ne_zero,inter_eq_left.mpr hsub]
  exact (Nat.prod_primeFactors_of_squarefree hsq).symm

/-- The elementary global cap used only for the rare common-prime error. -/
theorem coefficientWeight_le_scale (B n : ℕ) : coefficientWeight B n ≤ coefficientScale B := by
  classical
  have h : roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1/2) n ≤ (1 : ℝ) := by
    unfold roughSquarefreeWeight squarefreeWeight
    simp only [ArithmeticFunction.coe_mk]
    split_ifs
    · exact pow_le_one₀ (by norm_num) (by norm_num)
    all_goals norm_num
  exact (mul_le_mul_of_nonneg_left h (coefficientScale_nonneg B)).trans_eq (mul_one _)

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact equivalence of prime-site and prime-subset probabilities -/

namespace JointDickman

open Finset

theorem selectedPrimeSubset_subset (Q : Finset ℕ) (x : Q → Bool) :
    selectedPrimeSubset Q x ⊆ Q := filter_subset _ _

theorem retainedPrimeProduct_selected (Q : Finset ℕ) (x : Q → Bool) :
    retainedPrimeProduct Q x = ∏ p ∈ selectedPrimeSubset Q x, p := by
  have hfilter : Q.filter (fun p => p ∈ selectedPrimeSubset Q x) = selectedPrimeSubset Q x := by
    ext p
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => selectedPrimeSubset_subset Q x h
  calc
    _ = ∏ p : Q, if p.val ∈ selectedPrimeSubset Q x then p.val else 1 := by
      apply prod_congr rfl
      intro p _
      simp only [selectedPrimeSubset_mem]
    _ = ∏ p ∈ Q, if p ∈ selectedPrimeSubset Q x then p else 1 :=
      prod_coe_sort Q (fun p : ℕ => if p ∈ selectedPrimeSubset Q x then p else 1)
    _ = _ := by rw [prod_ite, hfilter]; simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedChannelMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of signed split masses and the actual channel -/

namespace JointDickman
open Finset

theorem retainedPrimeProduct_subset (P : Finset ℕ) (S : P.powerset) :
    retainedPrimeProduct P (subsetHitEquiv P S) = ∏ p ∈ S.val, p := by
  rw [retainedPrimeProduct_selected]
  congr 1
  ext p
  by_cases hp : p ∈ P
  · simp [selectedPrimeSubset, subsetHitEquiv, hp]
  · have hs : p ∉ S.val := fun hs => hp (mem_powerset.mp S.property hs)
    simp [selectedPrimeSubset, hp, hs]

theorem fullPrimeMass_subset (P : Finset ℕ) (S : P.powerset) :
    fullPrimeMass P (subsetHitEquiv P S) =
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S.val :=
by
  simpa only [fullPrimeMass, bernoulliSiteMass] using
    bernoulliSubsetMass_eq_product P (fun p : ℕ => 1/(p : ℝ)) S

/-- Push the finite signed split measure forward to its integer product. -/
theorem signedSplitProductMass_sum (P : Finset ℕ) (g : Finset ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P, signedSplitProductMass P g n * F n) =
      ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S *
        ∑ A ∈ P.powerset, subsetRetentionMass S A * F (∏ p ∈ A, p) := by
  classical
  unfold signedSplitProductMass splitProductMass
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S hS
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  rw [sum_eq_single (∏ p ∈ A, p)]
  · simp
    ring
  · intro n _ hn
    simp [Ne.symm hn]
  · intro hn
    exact False.elim (hn (mem_image.mpr ⟨A, hA, rfl⟩))

/-- The signed integer-product law is exactly the original fair-split expectation. -/
theorem signedSplitProductMass_expectation (P : Finset ℕ)
    (g : (P → Bool) → ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P,
      signedSplitProductMass P (subsetSiteTest P g) n * F n) =
      ∑ x : P → Bool, fullPrimeMass P x * g x *
        ∑ y : P → Bool, fairRetentionMass x y * F (retainedPrimeProduct P y) := by
  classical
  rw [signedSplitProductMass_sum]
  rw [← (subsetHitEquiv P).sum_comp]
  simp_rw [← (subsetHitEquiv P).sum_comp
    (fun y => fairRetentionMass _ y * F (retainedPrimeProduct P y))]
  simp_rw [fullPrimeMass_subset, fairRetentionMass_subsets, retainedPrimeProduct_subset]
  rw [← sum_coe_sort P.powerset]
  apply sum_congr rfl
  intro S _
  rw [sum_coe_sort P.powerset
    (fun A => subsetRetentionMass S.val A * F (∏ p ∈ A, p))]
  rfl

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SignedPairPushforward
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact two-endpoint fair-split pushforward -/

namespace JointDickman
open Finset

open Classical in
theorem signedSplitProductMass_zero_off_support (P : Finset ℕ)
    (g : Finset ℕ → ℝ) (n : ℕ) (hn : n ∉ primeSplitProductSupport P) :
    signedSplitProductMass P g n = 0 := by
  have hprod : ∀ A ∈ P.powerset, (∏ p ∈ A, p) ≠ n := by
    intro A hA he
    exact hn (mem_image.mpr ⟨A,hA,he⟩)
  unfold signedSplitProductMass
  apply sum_eq_zero
  intro S _
  have hz : splitProductMass P S n = 0 := by
    unfold splitProductMass
    apply sum_eq_zero
    intro A hA
    rw [ite_eq_right (hprod A hA),mul_zero]
  rw [hz,mul_zero]

open Classical in
theorem signedSplitProductMass_sum_on (P : Finset ℕ)
    (g : (P → Bool) → ℝ) (F : ℕ → ℝ) (A : Finset ℕ)
    (hA : primeSplitProductSupport P ⊆ A) :
    (∑ n ∈ A, signedSplitProductMass P (subsetSiteTest P g) n*F n) =
      ∑ x : P → Bool, fullPrimeMass P x*g x*
        ∑ y : P → Bool, fairRetentionMass x y*F (retainedPrimeProduct P y) := by
  rw [← signedSplitProductMass_expectation]
  symm
  apply sum_subset hA
  intro n _ hn
  rw [signedSplitProductMass_zero_off_support P _ n hn,zero_mul]

open Classical in
theorem signedSplitProductMass_pair_expectation (P : Finset ℕ)
    (g h : (P → Bool) → ℝ) (F : ℕ → ℕ → ℝ) (A D : Finset ℕ)
    (hA : primeSplitProductSupport P ⊆ A) (hD : primeSplitProductSupport P ⊆ D) :
    (∑ a ∈ A, ∑ d ∈ D,
      signedSplitProductMass P (subsetSiteTest P g) a*
        signedSplitProductMass P (subsetSiteTest P h) d*F a d) =
      ∑ x : P → Bool, ∑ z : P → Bool,
        fullPrimeMass P x*fullPrimeMass P z*g x*h z*
          ∑ y : P → Bool, ∑ w : P → Bool,
            fairRetentionMass x y*fairRetentionMass z w*
              F (retainedPrimeProduct P y) (retainedPrimeProduct P w) := by
  calc
    _ = ∑ a ∈ A, signedSplitProductMass P (subsetSiteTest P g) a*
        (∑ d ∈ D, signedSplitProductMass P (subsetSiteTest P h) d*F a d) := by
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ = ∑ x : P → Bool, fullPrimeMass P x*g x*
        ∑ y : P → Bool, fairRetentionMass x y*
          (∑ z : P → Bool, fullPrimeMass P z*h z*
            ∑ w : P → Bool, fairRetentionMass z w*
              F (retainedPrimeProduct P y) (retainedPrimeProduct P w)) := by
      rw [signedSplitProductMass_sum_on P g _ A hA]
      simp_rw [signedSplitProductMass_sum_on P h _ D hD]
    _ = _ := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      apply sum_congr rfl
      intro z _
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro w _
      ring

open Classical in
/-- The unsigned law pushed to products, retaining an arbitrary test. -/
theorem primeProductMass_sum_test (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P, primeProductMass P z n*F n) =
      ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) A*F (∏ p ∈ A,p) := by
  unfold primeSplitProductSupport
  rw [sum_image]
  · apply sum_congr rfl
    intro A hA
    rw [primeProductMass_at_product z hP (mem_powerset.mp hA)]
  · intro A hA D hD he
    exact primeProduct_injective hP (mem_powerset.mp hA) (mem_powerset.mp hD) he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_AmplificationFairKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth amplification sum as the actual fair-split kernel -/

namespace JointDickman
open Finset

theorem primeSplitProductSupport_subset_Ioc {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {U : ℕ} (hU : (∏ p ∈ P, p) ≤ U) :
    primeSplitProductSupport P ⊆ Ioc 0 U := by
  classical
  intro n hn
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hn
  have hAP := mem_powerset.mp hA
  refine mem_Ioc.mpr ⟨prod_pos (fun p hp => (hP p (hAP hp)).pos),?_⟩
  exact (prod_le_prod_of_subset_of_one_le' hAP (fun p hp _ => (hP p hp).one_le)).trans hU

open Classical in
theorem amplificationArithmeticTerm_factor (B j : ℕ) (T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) :
    amplificationArithmeticTerm B j T g h c b a =
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        amplificationScalarWeight B j T c b a := by
  unfold amplificationArithmeticTerm amplificationScalarWeight
  split_ifs <;> ring

open Classical in
theorem amplificationArithmeticSum_eq_fairKernel (B j : ℕ) (T : ℝ) (U V : ℕ)
    (hU : (∏ p ∈ auxiliaryPrimes B, p) ≤ U)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    amplificationArithmeticSum B j T U V g h =
      ∑ x : auxiliaryPrimes B → Bool, ∑ z : auxiliaryPrimes B → Bool,
        fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) z*g x*h z*
          amplificationFairKernel B j T V x z := by
  have hsupport := primeSplitProductSupport_subset_Ioc (auxiliaryPrimes_prime B) hU
  unfold amplificationArithmeticSum
  simp_rw [amplificationArithmeticTerm_factor]
  have hpair (c : ℕ) := signedSplitProductMass_pair_expectation (auxiliaryPrimes B) g h
    (fun a b => amplificationScalarWeight B j T c b a) (Ioc 0 U) (Ioc 0 U) hsupport hsupport
  have hreplace (c : ℕ) :
      (∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
          amplificationScalarWeight B j T c b a) =
      ∑ x : auxiliaryPrimes B → Bool, ∑ z : auxiliaryPrimes B → Bool,
        fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) z*g x*h z*
          ∑ y : auxiliaryPrimes B → Bool, ∑ w : auxiliaryPrimes B → Bool,
            fairRetentionMass x y*fairRetentionMass z w*
              amplificationScalarWeight B j T c
                (retainedPrimeProduct (auxiliaryPrimes B) w)
                (retainedPrimeProduct (auxiliaryPrimes B) y) := by
    rw [sum_comm]
    exact hpair c
  simp_rw [hreplace]
  unfold amplificationFairKernel
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro w _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationWeightBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique-quotient bound used when removing coprimality -/

namespace JointDickman
open Finset

open Classical in
theorem amplificationScalarWeight_bounds (B j : ℕ) (T : ℝ) (c b a : ℕ) :
    0 ≤ amplificationScalarWeight B j T c b a ∧
      amplificationScalarWeight B j T c b a ≤ coefficientScale B := by
  unfold amplificationScalarWeight
  split_ifs
  · have h1 := amplificationBump_bounds (Real.log c/B)
    have h2 := amplificationBump_bounds (a/(T*c))
    have h3 := amplificationBump_bounds (b/(T*c))
    have hprod : 0 ≤ amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c)) := mul_nonneg (mul_nonneg h1.1 h2.1) h3.1
    have hprod1 : amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c)) ≤ 1 := by
      calc
        _ ≤ (1 : ℝ)*1*1 := mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 (by norm_num))
          h3.2 h3.1 (by norm_num)
        _ = _ := by norm_num
    exact ⟨mul_nonneg (coefficientWeight_nonneg B c) hprod,
      (mul_le_of_le_one_right (coefficientWeight_nonneg B c) hprod1).trans
        (coefficientWeight_le_scale B c)⟩
  · exact ⟨le_rfl,coefficientScale_nonneg B⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockCandidates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite candidate representations determined by endpoint types -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem mem_endpointSplits {B L : ℕ} {τ C : ℝ} {S A : Finset ℕ} :
    A ∈ endpointSplits B L τ C S ↔
      A ⊆ S ∧ RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A) := by
  classical
  simp [endpointSplits]

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

theorem finiteExpectation_sum {J : Type*} [Fintype J] (w : Ω → ℝ) (f : J → Ω → ℝ) :
    finiteExpectation w (fun x => ∑ j, f j x) = ∑ j, finiteExpectation w (f j) := by
  simp only [finiteExpectation, mul_sum]
  exact sum_comm

theorem finiteExpectation_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) : finiteExpectation w f ≤ finiteExpectation w g := by
  exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hw x)

end Expectation

section IndependentSites

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- The finite sum-product identity supplies independence, with no probabilistic input. -/
theorem siteProduct_expectation_prod (p f : ι → A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => ∏ i, f i (x i)) =
      ∏ i, finiteExpectation (p i) (f i) := by
  simp only [finiteExpectation, siteProductMass, ← prod_mul_distrib]
  simpa using (prod_univ_sum (fun _ : ι => (univ : Finset A))
    (fun i a => p i a * f i a)).symm

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

end ConditionalSite

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingTransfer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateForwardMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forward candidate mass and the vanishing independent-root error -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

/-- The forward entry is zero once its lag is outside the candidate support. -/
theorem latentCandidateKernel_forward_zero {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i k : Fin M)
    (hik : i < k) (hlag : T ≤ k.val-i.val) :
    latentCandidateKernel B L T H M τ C S χ i k = 0 := by
  classical
  rw [latentCandidateKernel_pair B L T H τ C S χ i k hik]
  apply sum_eq_zero
  intro A _
  apply sum_eq_zero
  intro D _
  have hn : ¬ BlockCandidateAdmissible B L T H τ C ((i,k),(A,D)) := by
    intro he
    have ht := he.2.2.1
    change k.val-i.val < T at ht
    omega
  exact ite_eq_right hn

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductGcdError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing GCD restrictions on two independent selected prime products

The probability of a common selected prime is bounded by the sum of the
products of the two marginal hit probabilities. For the independent
`1/(2p)` selection laws this is at most `1/(4N)` when all allowed primes
exceed `N`. The same bound controls any bounded test of the selected pair.
-/

namespace JointDickman

open Finset PublishedInputs

/-- If the two endpoints are coprime, the additive coefficient is coprime
to each endpoint as well. This does not require a restriction on the lag. -/
theorem additive_triple_coprime_iff {a b c j : ℕ} (heq : a = b + j * c) :
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ↔ a.Coprime b := by
  constructor
  · exact And.left
  · intro hab
    have hba : b.Coprime (b + j * c) := by simpa only [← heq] using hab.symm
    have hbc : b.Coprime c :=
      (Nat.coprime_self_add_right.mp hba).coprime_dvd_right (dvd_mul_left c j)
    have hac : a.Coprime c := by
      rw [heq, Nat.coprime_add_mul_right_left]
      exact hbc
    exact ⟨hab, hac, hbc⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SignedProductGcd
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coprimality removal for the actual signed product masses -/

namespace JointDickman
open Finset Filter

open Classical in
theorem primeProductMass_pair_sum_test (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (F : ℕ → ℕ → ℝ) :
    (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      primeProductMass P z a*primeProductMass P z b*F a b) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P (fun p => z/p) A*
          bernoulliSubsetMass P (fun p => z/p) D*F (∏ p ∈ A,p) (∏ p ∈ D,p) := by
  calc
    _ = ∑ a ∈ primeSplitProductSupport P, primeProductMass P z a*
        (∑ b ∈ primeSplitProductSupport P, primeProductMass P z b*F a b) := by
      simp_rw [mul_sum,mul_assoc]
    _ = ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) A*
        (∑ D ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) D*
          F (∏ p ∈ A,p) (∏ p ∈ D,p)) := by
      rw [primeProductMass_sum_test P hP]
      simp_rw [primeProductMass_sum_test P hP]
    _ = _ := by simp_rw [mul_sum,mul_assoc]

open Classical in
/-- The product weight sums the unique additive coefficient before the two
endpoint laws are pushed forward. -/
theorem amplificationFairKernel_product_expectation (B j : ℕ) (T : ℝ) (V : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    (∑ x : auxiliaryPrimes B → Bool, ∑ z : auxiliaryPrimes B → Bool,
      fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) z*g x*h z*
        amplificationFairKernel B j T V x z) =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
          signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
            amplificationProductWeight B j T V a b := by
  have hinner (x z : auxiliaryPrimes B → Bool) :
      (∑ y : auxiliaryPrimes B → Bool, ∑ w : auxiliaryPrimes B → Bool,
        fairRetentionMass x y*fairRetentionMass z w*
          amplificationProductWeight B j T V
            (retainedPrimeProduct (auxiliaryPrimes B) y)
            (retainedPrimeProduct (auxiliaryPrimes B) w)) =
      amplificationFairKernel B j T V x z := by
    unfold amplificationProductWeight amplificationFairKernel
    simp_rw [mul_sum]
    simp_rw [sum_comm (s := univ) (t := Ioc 0 V)]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro w _
    ring
  rw [signedSplitProductMass_pair_expectation (auxiliaryPrimes B) g h
    (amplificationProductWeight B j T V) _ _ (Subset.refl _) (Subset.refl _)]
  simp_rw [hinner]


theorem amplification_gcd_rate_tendsto :
    Filter.Tendsto (fun B : ℕ => (amplificationMultiplier B : ℝ)*
      (((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))))
      Filter.atTop (nhds 0) := by
  have ht := ((tendsto_pow_atTop (by norm_num : (997 : ℕ) ≠ 0)).comp
    tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun B : ℕ => (B : ℝ)^997) Filter.atTop Filter.atTop)
  have hlim : Filter.Tendsto (fun B : ℕ => (1/4 : ℝ)*((B : ℝ)^997)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp ht).const_mul (1/4 : ℝ)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun B => mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg _))
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))) _ hlim
  filter_upwards [coefficientScale_eventually_le,amplificationMultiplier_comparable,
    Filter.eventually_gt_atTop 1] with B hscale hmul hB
  have hBr : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hT : (amplificationMultiplier B : ℝ) ≤ B := hmul.2.2.trans (by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hBr.le (by norm_num : (8/25 : ℝ) ≤ 1)))
  calc
    _ ≤ (B : ℝ)*(((B : ℝ)*B)/(4*(auxiliaryCutoff B : ℝ))) := by
      apply mul_le_mul hT
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hB0.le)
          (by positivity)
      · exact div_nonneg (mul_nonneg hB0.le (coefficientScale_nonneg B)) (by positivity)
      · exact hB0.le
    _ = (1/4 : ℝ)*((B : ℝ)^997)⁻¹ := by
      simp only [auxiliaryCutoff,Nat.cast_pow]
      have hp : (B : ℝ)^1000 = (B : ℝ)^997*(B : ℝ)^3 := by rw [← pow_add]
      rw [hp]
      field_simp

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateMultiplicity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping representation multiplicity in the latent second moment -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentCandidateKernel_representation_sum (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (i k : Fin M) (hik : i < k) :
    latentCandidateKernel B L T H M τ C S χ i k =
      ∑ ab ∈ candidatePairRepresentations B L T H τ C i k (S i) (S k),
        candidateMeanWeight B L τ C S χ ((i,k),ab) := by
  rw [latentCandidateKernel_pair B L T H τ C S χ i k hik]
  simp only [candidatePairRepresentations,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CandidateCoefficientFactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the deterministic and remainder factors of a candidate -/

namespace JointDickman
open Finset Classical

theorem candidateMeanWeight_factor {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) :
    candidateMeanWeight B L τ C S χ e =
      candidateCoefficientFactor B L τ C χ e*
        regularResidueWeight B L τ C (S e.1.1 \ e.2.1)*
        regularResidueWeight B L τ C (S e.1.2 \ e.2.2) := by
  rw [candidateMeanWeight_eq]
  unfold candidateCoefficientFactor
  ring

theorem candidateCoefficientFactor_zero_left {B L M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hr : ¬ RegularPrimeSet B L τ C A) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D)) = 0 := by
  unfold candidateCoefficientFactor candidateLow
  rw [regularCoefficientWeight,coefficientPrimeSet_primeProduct hA,ite_eq_right hr]
  simp

theorem candidateCoefficientFactor_zero_right {B L M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) {A D : Finset ℕ}
    (hD : D ⊆ auxiliaryPrimes B) (hr : ¬ RegularPrimeSet B L τ C D) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D)) = 0 := by
  have hz : regularCoefficientWeight B L τ C (candidateHigh ((i,t),(A,D))) = 0 := by
    change regularCoefficientWeight B L τ C (∏ p ∈ D, p) = 0
    rw [regularCoefficientWeight,coefficientPrimeSet_primeProduct hD,ite_eq_right hr]
  simp only [candidateCoefficientFactor,hz,mul_zero,zero_div,zero_mul]


/-- The local site kernel is a sum of deterministic factors times the two
regular remainder weights. -/
theorem candidateSiteKernel_factor_sum {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t) (S R : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      ∑ ab ∈ candidatePairRepresentations B L T H τ C i t S R,
        candidateCoefficientFactor B L τ C χ ((i,t),ab)*
          regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2) := by
  unfold candidateSiteKernel
  rw [latentCandidateKernel_representation_sum B L T H M τ C _ χ i t hit]
  have hne : i ≠ t := ne_of_lt hit
  simp only [Function.update_of_ne hne,Function.update_self]
  apply sum_congr rfl
  intro ab _
  rw [candidateMeanWeight_factor]
  simp only [Function.update_of_ne hne,Function.update_self]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstRepresentationSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the kernel by a first coefficient pair -/

namespace JointDickman
open Finset Classical

/-- The unrestricted pair sum is exact: the coefficient and remainder
weights themselves impose the four endpoint regularity conditions. -/
theorem candidateSiteKernel_unrestricted_sum {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    (S R : Finset ℕ) (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
        if BlockCandidateAdmissible B L T H τ C ((i,t),ab) ∧ ab.1 ⊆ S ∧ ab.2 ⊆ R then
          candidateCoefficientFactor B L τ C χ ((i,t),ab)*
            regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
        else 0 := by
  rw [candidateSiteKernel_factor_sum χ i t hit S R]
  let J := (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset
  have hsub : candidatePairRepresentations B L T H τ C i t S R ⊆ J := by
    intro ab hab
    obtain ⟨ha,hd⟩ := mem_product.mp (mem_filter.mp hab).1
    exact mem_product.mpr ⟨mem_powerset.mpr ((mem_endpointSplits.mp ha).1.trans hS),
      mem_powerset.mpr ((mem_endpointSplits.mp hd).1.trans hR)⟩
  let w := fun ab : Finset ℕ × Finset ℕ =>
    if BlockCandidateAdmissible B L T H τ C ((i,t),ab) ∧ ab.1 ⊆ S ∧ ab.2 ⊆ R then
      candidateCoefficientFactor B L τ C χ ((i,t),ab)*
        regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
    else 0
  calc
    _ = ∑ ab ∈ candidatePairRepresentations B L T H τ C i t S R, w ab := by
      apply sum_congr rfl
      intro ab hab
      obtain ⟨hp,he⟩ := mem_filter.mp hab
      obtain ⟨ha,hd⟩ := mem_product.mp hp
      exact (ite_eq_left ⟨he,(mem_endpointSplits.mp ha).1,(mem_endpointSplits.mp hd).1⟩).symm
    _ = ∑ ab ∈ J, w ab := by
      apply sum_subset hsub
      intro ab hab hnot
      dsimp only [w]
      split_ifs with hc
      · have hpair := mem_product.mp hab
        have hA := mem_powerset.mp hpair.1
        have hD := mem_powerset.mp hpair.2
        by_cases ha : RegularPrimeSet B L τ C ab.1
        · by_cases hd : RegularPrimeSet B L τ C ab.2
          · by_cases hs : RegularPrimeSet B L τ C (S \ ab.1)
            · by_cases hr : RegularPrimeSet B L τ C (R \ ab.2)
              · exact False.elim (hnot (mem_filter.mpr ⟨mem_product.mpr
                  ⟨mem_endpointSplits.mpr ⟨hc.2.1,ha,hs⟩,
                   mem_endpointSplits.mpr ⟨hc.2.2,hd,hr⟩⟩,hc.1⟩))
              · simp only [regularResidueWeight,hr,ite_false, if_false,mul_zero]
            · simp only [regularResidueWeight,hs,ite_false, if_false,mul_zero,zero_mul]
          · rw [candidateCoefficientFactor_zero_right χ i t hD hd]
            simp
        · rw [candidateCoefficientFactor_zero_left χ i t hA ha]
          simp
      · rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateFairSplit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact fair-retention normalization of the latent candidate kernel -/

namespace JointDickman
open Finset


open Classical in
/-- The two regularity indicators are the only restrictions in the
arithmetic-to-fair normalization of an endpoint and its remainder. -/
theorem candidateCoefficientFactor_fair {B L M : ℕ} {τ C : ℝ}
    (hB : 1 < B) (χ : BlockCandidateIndex M → ℝ) (i t : Fin M)
    {S R A D : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B)
    (hAS : A ⊆ S) (hDR : D ⊆ R) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D))*
      regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D) =
    (B : ℝ)*independentRootMean B L τ C*subsetRetentionMass S A*subsetRetentionMass R D*
      (if (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
          (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)) then
        regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*χ ((i,t),(A,D))
      else 0) := by
  have hleft := regular_arithmetic_split_identity (L := L) (τ := τ) (C := C) hB hS hAS
  have hright := regular_arithmetic_split_identity (L := L) (τ := τ) (C := C) hB hR hDR
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  unfold candidateCoefficientFactor candidateLow candidateHigh
  calc
    _ = ((regularCoefficientWeight B L τ C (∏ p ∈ A,p)*
          regularResidueWeight B L τ C (S \ A))*
        (regularCoefficientWeight B L τ C (∏ p ∈ D,p)*
          regularResidueWeight B L τ C (R \ D))/(B : ℝ))*
        regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
        χ ((i,t),(A,D))*independentRootMean B L τ C := by ring
    _ = _ := by
      rw [hleft,hright]
      by_cases ha : RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)
      all_goals by_cases hd : RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)
      all_goals simp only [ha,hd,and_self,and_false,false_and,ite_true, if_true,ite_false, if_false,
        mul_zero,zero_mul]
      all_goals field_simp [hB0] <;> ring

open Classical in
/-- Exact candidate kernel on the ambient prime powerset. This form keeps
all restrictions visible before estimating the discarded regularity events. -/
theorem candidateSiteKernel_fair_sum {B L T H M : ℕ} {τ C : ℝ}
    (hB : 1 < B) (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    {S R : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      (B : ℝ)*independentRootMean B L τ C*
        ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
          subsetRetentionMass S A*subsetRetentionMass R D*
            (if BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) ∧
                (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
                (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)) then
              regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*χ ((i,t),(A,D))
            else 0) := by
  rw [candidateSiteKernel_unrestricted_sum χ i t hit S R hS hR,
    Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  by_cases hAS : A ⊆ S
  · by_cases hDR : D ⊆ R
    · by_cases had : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
      · rw [ite_eq_left ⟨had,hAS,hDR⟩,
          candidateCoefficientFactor_fair hB χ i t hS hR hAS hDR]
        simp only [had,true_and]
        ring
      · simp [had]
    · simp [hDR,subsetRetentionMass]
  · simp [hAS,subsetRetentionMass]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateScalarIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the arithmetic scalar with an admissible candidate -/

namespace JointDickman
open Finset

/-- The candidate quotient is the unique coefficient in its additive relation. -/
theorem candidateQuotient_of_relation {M : ℕ} {e : BlockCandidateIndex M} {c : ℕ}
    (hj : 0 < candidateLag e)
    (he : candidateHigh e = candidateLow e+candidateLag e*c) :
    candidateQuotient e = c := by
  unfold candidateQuotient
  rw [he,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left c hj]

open Classical in
theorem amplificationScalarWeight_support {B j T c b a : ℕ}
    (hB : 0 < B) (hT : 0 < T) (hc : 0 < c)
    (hw : amplificationScalarWeight B j T c b a ≠ 0) :
    a = b+j*c ∧ coefficientWeight B c ≠ 0 ∧
      (B : ℝ) ≤ Real.log c ∧ Real.log c ≤ 2*B ∧
      T*c ≤ b ∧ b ≤ 2*T*c ∧ T*c ≤ a ∧ a ≤ 2*T*c ∧
      c = ∏ p ∈ coefficientPrimeSet B c,p := by
  have he : a = b+j*c := by
    by_contra h
    exact hw (by simp [amplificationScalarWeight,h])
  rw [amplificationScalarWeight,ite_eq_left he] at hw
  obtain ⟨hcoef,hprod⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨hprod,hb⟩ := mul_ne_zero_iff.mp hprod
  obtain ⟨hlog,ha⟩ := mul_ne_zero_iff.mp hprod
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hTC : (0 : ℝ) < T*c := by positivity
  have hl := amplificationBump_support hlog
  have hla := amplificationBump_support ha
  have hlb := amplificationBump_support hb
  have hloglo : (B : ℝ) ≤ Real.log c := by
    have := (lt_div_iff₀ hBr).mp hl.1
    linarith
  have hloghi : Real.log c ≤ 2*B := ((div_lt_iff₀ hBr).mp hl.2).le
  have hlo (n : ℕ) (h : 1 < (n : ℝ)/(T*c)) : T*c ≤ n := by
    have := (lt_div_iff₀ hTC).mp h
    have hn : (T : ℝ)*c ≤ n := by simpa only [one_mul] using this.le
    exact_mod_cast hn
  have hhi (n : ℕ) (h : (n : ℝ)/(T*c) < 2) : n ≤ 2*T*c := by
    have hh := (div_lt_iff₀ hTC).mp h
    have hn : (n : ℝ) ≤ 2*(T : ℝ)*c := by simpa only [mul_assoc] using hh.le
    exact_mod_cast hn
  refine ⟨he,hcoef,hloglo,hloghi,hlo b hlb.1,hhi b hlb.2,
    hlo a hla.1,hhi a hla.2,?_⟩
  apply coefficientWeight_eq_primeProduct hcoef
  change (c : ℝ) ≤ Real.exp (4*(B : ℝ))
  rw [← Real.exp_log hcr]
  apply Real.exp_le_exp.mpr
  linarith

open Classical in
/-- Once the three retained coefficients are regular and the endpoints are
coprime, every nonzero smooth arithmetic summand is an actual candidate. -/
theorem candidateAdmissible_of_scalar {B L T H M c : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hc : 0 < c)
    {i t : Fin M} (hit : i < t) {A D : Finset ℕ}
    (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    (hw : amplificationScalarWeight B (t.val-i.val) T c
      (∏ p ∈ A,p) (∏ p ∈ D,p) ≠ 0)
    (hcop : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p))
    (hreg : RegularPrimeSet B L τ C (coefficientPrimeSet B c)) :
    BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) := by
  obtain ⟨he,hcoef,hlo,hhi,hbl,hbu,hal,hau,hprod⟩ :=
    amplificationScalarWeight_support hB hT hc hw
  have hj : 0 < candidateLag ((i,t),(A,D)) := by
    change 0 < t.val-i.val
    exact Nat.sub_pos_of_lt hit
  have heq : candidateHigh ((i,t),(A,D)) =
      candidateLow ((i,t),(A,D))+candidateLag ((i,t),(A,D))*c := he
  have hq := candidateQuotient_of_relation hj heq
  have hcop' := (additive_triple_coprime_iff he).mpr hcop.symm
  unfold BlockCandidateAdmissible
  rw [hq]
  exact ⟨hit,hH,hjT,hc,heq,hcop,hcop'.2.2,hcop'.2.1,hprod,hreg,
    hlo,hhi,hbl,hbu,hal,hau⟩


open Classical in
/-- The candidate restrictions impose no extra condition on a nonzero
smooth summand once coprimality and coefficient regularity are retained. -/
theorem regularCandidateScalar_eq_of_relation {B L T H M c : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hc : 0 < c)
    {i t : Fin M} (hit : i < t) {A D : Finset ℕ}
    (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    (he : (∏ p ∈ D,p) = (∏ p ∈ A,p)+(t.val-i.val)*c) :
    regularCandidateScalar B L T H τ C ((i,t),(A,D)) =
      if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
          RegularPrimeSet B L τ C (coefficientPrimeSet B c) then
        amplificationScalarWeight B (t.val-i.val) T c (∏ p ∈ A,p) (∏ p ∈ D,p)
      else 0 := by
  have hj : 0 < candidateLag ((i,t),(A,D)) := Nat.sub_pos_of_lt hit
  have hq : candidateQuotient ((i,t),(A,D)) = c := candidateQuotient_of_relation hj he
  have hcut : candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T)
      ((i,t),(A,D)) =
      amplificationBump (Real.log c/B)*amplificationBump ((∏ p ∈ D,p : ℕ)/(T*c : ℝ))*
        amplificationBump ((∏ p ∈ A,p : ℕ)/(T*c : ℝ)) := by
    simp only [candidateCutoff,amplificationOuterWeight,amplificationInnerWeight,
      hq,candidateHigh,candidateLow]
  by_cases ha : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
  · have hp : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c) := by
      exact ⟨ha.2.2.2.2.2.1,by simpa only [hq] using ha.2.2.2.2.2.2.2.2.2.1⟩
    rw [regularCandidateScalar,ite_eq_left ha,ite_eq_left hp,hq,hcut,
      regularCoefficientWeight,ite_eq_left hp.2,
      amplificationScalarWeight,ite_eq_left he]
  · rw [regularCandidateScalar,ite_eq_right ha]
    by_cases hp : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c)
    · rw [ite_eq_left hp]
      symm
      by_contra hw
      exact ha (candidateAdmissible_of_scalar hB hT hc hit hH hjT hw hp.1 hp.2)
    · rw [ite_eq_right hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateScalarSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the unique additive coefficient in the candidate kernel -/

namespace JointDickman
open Finset

open Classical in
theorem regularCandidateScalar_eq_sum {B L T H M V : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T)
    (hV : ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V)
    {i t : Fin M} (hit : i < t) {A D : Finset ℕ}
    (hH : H < t.val-i.val) (hjT : t.val-i.val < T) :
    regularCandidateScalar B L T H τ C ((i,t),(A,D)) =
      ∑ c ∈ Ioc 0 V, regularArithmeticScalar B L (t.val-i.val) τ C T c
        (∏ p ∈ A,p) (∏ p ∈ D,p) := by
  have hj : 0 < candidateLag ((i,t),(A,D)) := Nat.sub_pos_of_lt hit
  symm
  by_cases ha : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
  · rcases ha with ⟨_,_,_,hq,he,_,_,_,_,_,_,hqhi,_,_,_,_⟩
    have hmem : candidateQuotient ((i,t),(A,D)) ∈ Ioc 0 V := by
      refine mem_Ioc.mpr ⟨hq,?_⟩
      apply le_trans _ hV
      apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
      rw [← Real.exp_log (by exact_mod_cast hq : (0 : ℝ) < candidateQuotient ((i,t),(A,D)))]
      exact Real.exp_le_exp.mpr hqhi
    rw [sum_eq_single (candidateQuotient ((i,t),(A,D)))]
    · exact (regularCandidateScalar_eq_of_relation hB hT hq hit hH hjT he).symm
    · intro c hc hne
      by_contra hn
      have hp : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
          RegularPrimeSet B L τ C (coefficientPrimeSet B c) := by
        by_contra hp
        exact hn (by simp only [regularArithmeticScalar,ite_eq_right hp])
      have hw : amplificationScalarWeight B (t.val-i.val) T c
          (∏ p ∈ A,p) (∏ p ∈ D,p) ≠ 0 := by
        simpa only [regularArithmeticScalar,ite_eq_left hp] using hn
      have hec := (amplificationScalarWeight_support hB hT (mem_Ioc.mp hc).1 hw).1
      exact hne (candidateQuotient_of_relation hj hec).symm
    · intro hnot
      exact False.elim (hnot hmem)
  · rw [regularCandidateScalar,ite_eq_right ha]
    apply sum_eq_zero
    intro c hc
    by_cases hp : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c)
    · rw [regularArithmeticScalar,ite_eq_left hp]
      by_contra hw
      exact ha (candidateAdmissible_of_scalar hB hT (mem_Ioc.mp hc).1 hit hH hjT hw hp.1 hp.2)
    · exact ite_eq_right hp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RemainderFailureWeight
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted failure estimate on the smooth coefficient support -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem weighted_remainder_failure
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → ∀ F : Finset ℕ → Finset ℕ → ℝ,
          (∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
            0 ≤ F A D) →
          (∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
            F A D ≠ 0 → (∏ p ∈ A,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
              (∏ p ∈ D,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B)) →
          (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
            F A D*fairRemainingPairFailure B L τ C A D) ≤
          K*(ε B+Real.exp (-(1/10 : ℝ)*C))*
            (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*F A D) := by
  obtain ⟨K,hK,hloss⟩ := fair_remaining_pair_regularity_loss hM
    (by norm_num : (0 : ℝ) < 16/5)
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss] with B hb
  intro C hC F hF hs
  simp_rw [mul_sum]
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  by_cases hz : F A D = 0
  · simp only [hz,zero_mul,mul_zero]
    exact le_rfl
  · have hsize := hs A hA D hD hz
    have hh := mul_le_mul_of_nonneg_left
      (hb A D C hC (mem_powerset.mp hA) (mem_powerset.mp hD) hsize.1 hsize.2) (hF A hA D hD)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RemainderPushforward
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact selected-and-remaining law behind the candidate error -/

namespace JointDickman
open Finset

open Classical in
theorem selectedRemainingMass_site {P S A : Finset ℕ} (hA : A ⊆ S) :
    bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*subsetRetentionMass S A =
      fairSelectedRemainingMass P A (S \ A) := by
  have hd : Disjoint A (S \ A) := by
    apply disjoint_left.mpr
    intro p hp hps
    exact (mem_sdiff.mp hps).2 hp
  simp only [subsetRetentionMass,ite_eq_left hA,fairSelectedRemainingMass,
    ite_eq_left hd,union_sdiff_of_subset hA]

open Classical in
/-- Replacing a site by its selected set and its complement is an exact
change of variables. The test can be a regularity failure indicator. -/
theorem selectedRemainingMass_sum {P A : Finset ℕ} (hA : A ⊆ P)
    (F : Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*
      subsetRetentionMass S A*F (S \ A)) =
      ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R*F R := by
  have hsub : (P \ A).powerset ⊆ P.powerset := by
    intro R hR
    exact mem_powerset.mpr ((mem_powerset.mp hR).trans sdiff_subset)
  have hext : (∑ R ∈ (P \ A).powerset, fairSelectedRemainingMass P A R*F R) =
      ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R*F R := by
    apply sum_subset hsub
    intro R hR hn
    have hd : ¬ Disjoint A R := by
      intro hd
      apply hn
      apply mem_powerset.mpr
      intro p hp
      exact mem_sdiff.mpr ⟨mem_powerset.mp hR hp,
        fun ha => disjoint_left.mp hd ha hp⟩
    simp only [fairSelectedRemainingMass,ite_eq_right hd,zero_mul]
  rw [← hext]
  calc
    _ = ∑ S ∈ P.powerset.filter (fun S => A ⊆ S),
        bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*subsetRetentionMass S A*F (S \ A) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro S _
      by_cases hs : A ⊆ S
      · rw [ite_eq_left hs]
      · simp only [subsetRetentionMass,ite_eq_right hs,mul_zero,zero_mul]
    _ = _ := by
      apply sum_bij (fun S _ => S \ A)
      · intro S hS
        exact mem_powerset.mpr (sdiff_subset_sdiff
          (mem_powerset.mp (mem_filter.mp hS).1) subset_rfl)
      · intro S hS T hT he
        have hs := sdiff_union_of_subset (mem_filter.mp hS).2
        have ht := sdiff_union_of_subset (mem_filter.mp hT).2
        rw [he] at hs
        exact hs.symm.trans ht
      · intro R hR
        have hr := mem_powerset.mp hR
        refine ⟨A ∪ R,mem_filter.mpr ⟨mem_powerset.mpr
          (union_subset hA (hr.trans sdiff_subset)),subset_union_left⟩,?_⟩
        ext p
        have hp : p ∈ R → p ∉ A := fun h => (mem_sdiff.mp (hr h)).2
        simp only [mem_sdiff,mem_union]
        tauto
      · intro S hS
        rw [selectedRemainingMass_site (mem_filter.mp hS).2]


open Classical in
theorem selectedRemainingMass_pair_sum {P A D : Finset ℕ} (hA : A ⊆ P) (hD : D ⊆ P)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) R*
      subsetRetentionMass S A*subsetRetentionMass R D*F (S \ A) (R \ D)) =
      ∑ U ∈ P.powerset, ∑ V ∈ P.powerset,
        fairSelectedRemainingMass P A U*fairSelectedRemainingMass P D V*F U V := by
  calc
    _ = ∑ S ∈ P.powerset,
        bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*subsetRetentionMass S A*
          (∑ R ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) R*
            subsetRetentionMass R D*F (S \ A) (R \ D)) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      ring
    _ = ∑ S ∈ P.powerset,
        bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*subsetRetentionMass S A*
          (∑ V ∈ P.powerset, fairSelectedRemainingMass P D V*F (S \ A) V) := by
      simp_rw [selectedRemainingMass_sum hD]
    _ = ∑ U ∈ P.powerset, fairSelectedRemainingMass P A U*
        (∑ V ∈ P.powerset, fairSelectedRemainingMass P D V*F U V) :=
      selectedRemainingMass_sum hA (fun U =>
        ∑ V ∈ P.powerset, fairSelectedRemainingMass P D V*F U V)
    _ = _ := by simp_rw [mul_sum,mul_assoc]

open Classical in
/-- The bad-remainder event in the site-first expression is exactly the
failure mass whose conditional probability is controlled by Mertens. -/
theorem remainingPairFailure_site_sum (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
      subsetRetentionMass S A*subsetRetentionMass R D*
        (if RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
          then 0 else 1)) = fairRemainingPairFailure B L τ C A D := by
  rw [selectedRemainingMass_pair_sum hA hD (fun U V =>
    if RegularPrimeSet B L τ C U ∧ RegularPrimeSet B L τ C V then 0 else 1)]
  unfold fairRemainingPairFailure
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro V _
  split_ifs <;> simp only [mul_zero,mul_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SignedRemainderError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed site tests in the removal of the two remainder restrictions -/

namespace JointDickman
open Finset

open Classical in
theorem signed_remaining_pair_error (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (g h : Finset ℕ → ℝ) (hg : ∀ S, |g S| ≤ 1) (hh : ∀ R, |h R| ≤ 1) (F : ℝ) :
    |(∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*
        subsetRetentionMass S A*subsetRetentionMass R D*F)-
      (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        if RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D) then
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*
          subsetRetentionMass S A*subsetRetentionMass R D*F else 0)| ≤
      |F| *fairRemainingPairFailure B L τ C A D := by
  let P := auxiliaryPrimes B
  let μ := bernoulliSubsetMass P (fun p => 1/(p : ℝ))
  let w := fun S R => μ S*μ R*subsetRetentionMass S A*subsetRetentionMass R D
  let E := fun S R => RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
  have hμ (S : Finset ℕ) (hS : S ∈ P.powerset) : 0 ≤ μ S := by
    apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr (by linarith)⟩
  have hr (S A : Finset ℕ) : 0 ≤ subsetRetentionMass S A := by
    unfold subsetRetentionMass
    split_ifs <;> positivity
  have hw (S R : Finset ℕ) (hS : S ∈ P.powerset) (hR : R ∈ P.powerset) : 0 ≤ w S R :=
    mul_nonneg (mul_nonneg (mul_nonneg (hμ S hS) (hμ R hR)) (hr S A)) (hr R D)
  have he :
      (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, μ S*μ R*g S*h R*
        subsetRetentionMass S A*subsetRetentionMass R D*F)-
      (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, if E S R then μ S*μ R*g S*h R*
        subsetRetentionMass S A*subsetRetentionMass R D*F else 0) =
      ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        if E S R then 0 else w S R*g S*h R*F := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro S _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro R _
    dsimp only [w]
    split_ifs <;> ring
  change |(∑ S ∈ P.powerset, ∑ R ∈ P.powerset, μ S*μ R*g S*h R*
      subsetRetentionMass S A*subsetRetentionMass R D*F)-
    (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, if E S R then μ S*μ R*g S*h R*
      subsetRetentionMass S A*subsetRetentionMass R D*F else 0)| ≤ _
  rw [he]
  calc
    _ ≤ ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        |if E S R then 0 else w S R*g S*h R*F| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun S _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        w S R*|F| *(if E S R then 0 else 1) := by
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro R hR
      by_cases hE : E S R
      · rw [ite_eq_left hE,ite_eq_left hE,abs_zero,mul_zero]
      · rw [ite_eq_right hE,ite_eq_right hE,mul_one]
        simp only [abs_mul,abs_of_nonneg (hw S R hS hR)]
        have hgh : |g S| *|h R| ≤ 1 :=
          (mul_le_mul (hg S) (hh R) (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
        calc
          _ = w S R*(|g S| *|h R|)*|F| := by ring
          _ ≤ w S R*1*|F| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgh (hw S R hS hR))
              (abs_nonneg F)
          _ = _ := by ring
    _ = |F| *(∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        w S R*(if E S R then 0 else 1)) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      ring
    _ = _ := by
      rw [show (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        w S R*(if E S R then 0 else 1)) = fairRemainingPairFailure B L τ C A D from
        remainingPairFailure_site_sum B L τ C hA hD]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RemainderKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing remainder regularity in the actual finite retention kernel -/

namespace JointDickman
open Finset

private theorem four_subset_sums_swap (P : Finset ℕ)
    (f : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
      f S R A D) =
    ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
      f S R A D := by
  conv_lhs => arg 2; ext S; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext A; arg 2; ext S; rw [sum_comm]
  conv_lhs => arg 2; ext A; rw [sum_comm]

open Classical in
theorem retentionKernel_remaining_error (B L : ℕ) (τ C : ℝ)
    (F : Finset ℕ → Finset ℕ → ℝ)
    (g h : Finset ℕ → ℝ) (hg : ∀ S, |g S| ≤ 1) (hh : ∀ R, |h R| ≤ 1) :
    |(∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*
          retainedSubsetKernel (auxiliaryPrimes B) F S R)-
      (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*
          regularRemainderKernel B L τ C F S R)| ≤
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        |F A D| *fairRemainingPairFailure B L τ C A D := by
  let P := auxiliaryPrimes B
  let μ := bernoulliSubsetMass P (fun p => 1/(p : ℝ))
  let v := fun S R A D => μ S*μ R*g S*h R*subsetRetentionMass S A*subsetRetentionMass R D*F A D
  let E := fun S R A D => RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
  have he :
      (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, μ S*μ R*g S*h R*retainedSubsetKernel P F S R)-
      (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, μ S*μ R*g S*h R*regularRemainderKernel B L τ C F S R) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        ((∑ S ∈ P.powerset, ∑ R ∈ P.powerset, v S R A D)-
          ∑ S ∈ P.powerset, ∑ R ∈ P.powerset, if E S R A D then v S R A D else 0) := by
    have hfull : (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        μ S*μ R*g S*h R*retainedSubsetKernel P F S R) =
        ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
          v S R A D := by
      rw [← four_subset_sums_swap]
      unfold retainedSubsetKernel
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro D _
      dsimp only [v]
      ring
    have hregular : (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        μ S*μ R*g S*h R*regularRemainderKernel B L τ C F S R) =
        ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
          if E S R A D then v S R A D else 0 := by
      rw [← four_subset_sums_swap]
      unfold regularRemainderKernel
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro D _
      dsimp only [v,E]
      split_ifs <;> ring
    rw [hfull,hregular,← sum_sub_distrib]
    apply sum_congr rfl
    intro A _
    rw [sum_sub_distrib]
  change |(∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
      μ S*μ R*g S*h R*retainedSubsetKernel P F S R)-
    (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
      μ S*μ R*g S*h R*regularRemainderKernel B L τ C F S R)| ≤ _
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro A hA
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro D hD
  exact signed_remaining_pair_error B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD) g h hg hh (F A D)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RemainderKernelEstimate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published remainder-regularity estimate for bounded signed site tests -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem remainderKernel_regularity_estimate
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → ∀ F : Finset ℕ → Finset ℕ → ℝ,
          (∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
            0 ≤ F A D) →
          (∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
            F A D ≠ 0 → (∏ p ∈ A,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
              (∏ p ∈ D,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B)) →
          ∀ g h : Finset ℕ → ℝ, (∀ S, |g S| ≤ 1) → (∀ R, |h R| ≤ 1) →
          |subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B) F)-
            subsetKernelBilinear B g h (regularRemainderKernel B L τ C F)| ≤
          K*(ε B+Real.exp (-(1/10 : ℝ)*C))*
            (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*F A D) := by
  obtain ⟨K,hK,hloss⟩ := weighted_remainder_failure hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss] with B hb
  intro C hC F hF hs g h hg hh
  calc
    _ ≤ ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        |F A D| *fairRemainingPairFailure B L τ C A D :=
      retentionKernel_remaining_error B L τ C F g h hg hh
    _ = ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        F A D*fairRemainingPairFailure B L τ C A D := by
      apply sum_congr rfl
      intro A hA
      apply sum_congr rfl
      intro D hD
      rw [abs_of_nonneg (hF A hA D hD)]
    _ ≤ _ := hb C hC F hF hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateRetentionKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The candidate coefficient weight for the remainder-regularity estimate -/

namespace JointDickman
open Finset

open Classical in
theorem candidateRetainedWeight_bounds (B L j : ℕ) (τ C : ℝ) (T V : ℕ) (A D : Finset ℕ) :
    0 ≤ candidateRetainedWeight B L j τ C T V A D ∧
      candidateRetainedWeight B L j τ C T V A D ≤
        amplificationProductWeight B j T V (∏ p ∈ D,p) (∏ p ∈ A,p) := by
  have hscalar (c : ℕ) :
      0 ≤ regularArithmeticScalar B L j τ C T c (∏ p ∈ A,p) (∏ p ∈ D,p) ∧
      regularArithmeticScalar B L j τ C T c (∏ p ∈ A,p) (∏ p ∈ D,p) ≤
        amplificationScalarWeight B j T c (∏ p ∈ A,p) (∏ p ∈ D,p) := by
    unfold regularArithmeticScalar
    split_ifs
    · exact ⟨(amplificationScalarWeight_bounds ..).1,le_rfl⟩
    · exact ⟨le_rfl,(amplificationScalarWeight_bounds ..).1⟩
  unfold candidateRetainedWeight amplificationProductWeight
  split_ifs
  · exact ⟨mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun c _ => (hscalar c).1)),
      mul_le_mul_of_nonneg_left (sum_le_sum (fun c _ => (hscalar c).2)) (Nat.cast_nonneg _)⟩
  · exact ⟨le_rfl,mul_nonneg (Nat.cast_nonneg _)
      (sum_nonneg (fun c _ => (amplificationScalarWeight_bounds ..).1))⟩

open Classical in
theorem candidateRetainedWeight_support {B L j T V : ℕ} {τ C : ℝ}
    (hB : 30 ≤ B) (hT : 0 < T) (hlogT : Real.log T ≤ (B : ℝ)/10)
    {A D : Finset ℕ} (hw : candidateRetainedWeight B L j τ C T V A D ≠ 0) :
    (∏ p ∈ A,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      (∏ p ∈ D,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) := by
  have hweight := candidateRetainedWeight_bounds B L j τ C T V A D
  have hprod : amplificationProductWeight B j T V (∏ p ∈ D,p) (∏ p ∈ A,p) ≠ 0 := by
    intro hz
    exact hw (le_antisymm (hweight.2.trans_eq hz) hweight.1)
  unfold amplificationProductWeight at hprod
  obtain ⟨c,hc,hcne⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hprod)
  obtain ⟨_,_,_,hclog,hlo,hhi,ha,had,_⟩ := amplificationScalarWeight_support
    (show 0 < B by omega) hT (mem_Ioc.mp hc).1 hcne
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hcr : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
  have hTexp : (T : ℝ) ≤ Real.exp ((B : ℝ)/10) := by
    rw [← Real.exp_log hTr]
    exact Real.exp_le_exp.mpr hlogT
  have hcexp : (c : ℝ) ≤ Real.exp (2*(B : ℝ)) := by
    rw [← Real.exp_log hcr]
    exact Real.exp_le_exp.mpr hclog
  have htwo : (2 : ℝ) ≤ Real.exp ((11/10 : ℝ)*B) := by
    have hh := Real.add_one_le_exp ((11/10 : ℝ)*B)
    linarith
  have hupper : (2*T*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) := by
    have hh : (2 : ℝ)*T*c ≤
        Real.exp ((11/10 : ℝ)*B)*Real.exp ((B : ℝ)/10)*Real.exp (2*(B : ℝ)) :=
      mul_le_mul (mul_le_mul htwo hTexp (Nat.cast_nonneg _) (Real.exp_pos _).le)
        hcexp (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    have he : Real.exp ((11/10 : ℝ)*B)*Real.exp ((B : ℝ)/10)*Real.exp (2*(B : ℝ)) =
        Real.exp ((16/5 : ℝ)*B) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    rw [he] at hh
    exact_mod_cast hh
  exact ⟨(by exact_mod_cast hhi : ((∏ p ∈ A,p : ℕ) : ℝ) ≤ (2*T*c : ℕ)).trans hupper,
    (by exact_mod_cast had : ((∏ p ∈ D,p : ℕ) : ℝ) ≤ (2*T*c : ℕ)).trans hupper⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateMeanBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive arithmetic mass dominating the candidate remainder error -/

namespace JointDickman
open Finset

open Classical in
theorem amplification_positive_product_mass (B j T U V : ℕ)
    (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U) :
    (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*
      amplificationProductWeight B j T V (∏ p ∈ D,p) (∏ p ∈ A,p)) =
      amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
  have hs := amplificationArithmeticSum_eq_fairKernel B j T U V hU (fun _ => 1) (fun _ => 1)
  rw [amplificationFairKernel_product_expectation] at hs
  have htest : subsetSiteTest (auxiliaryPrimes B) (fun _ => (1 : ℝ)) = (fun _ => 1) := rfl
  rw [htest] at hs
  simp_rw [signedSplitProductMass_one] at hs
  rw [hs,primeProductMass_pair_sum_test (auxiliaryPrimes B) (auxiliaryPrimes_prime B)]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  ring

open Classical in
theorem candidateRetainedWeight_positive_mass_le (B L j T U V : ℕ) (τ C : ℝ)
    (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U) :
    (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*
      candidateRetainedWeight B L j τ C T V A D) ≤
      amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
  rw [← amplification_positive_product_mass B j T U V hU]
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  have hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ (1/2 : ℝ)/p ∧ (1/2 : ℝ)/p ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr (by linarith)⟩
  exact mul_le_mul_of_nonneg_left (candidateRetainedWeight_bounds B L j τ C T V A D).2
    (mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hA) hq)
      (bernoulliSubsetMass_nonneg (mem_powerset.mp hD) hq))

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

theorem candidateSiteKernel_zero_of_far {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (a b : Finset ℕ)
    (hfar : T ≤ Nat.dist i.val k.val) :
    candidateSiteKernel B L T H M τ C χ i k a b = 0 := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · rw [Nat.dist_eq_sub_of_le hik.le] at hfar
    exact latentCandidateKernel_forward_zero _ _ _ _ hik hfar
  · exact candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _
  · rw [candidateSiteKernel_symm]
    rw [Nat.dist_eq_sub_of_le_right hki.le] at hfar
    exact latentCandidateKernel_forward_zero _ _ _ _ hki hfar

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LatentSquareSymmetry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetry and lag support of the integrated edge square -/

namespace JointDickman
open Finset Classical

theorem candidateSiteKernel_zero_of_short {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (S R : Finset ℕ)
    (hshort : Nat.dist i.val t.val ≤ H) :
    candidateSiteKernel B L T H M τ C χ i t S R = 0 := by
  have hf (i t : Fin M) (hit : i < t) (S R : Finset ℕ)
      (hshort : t.val-i.val ≤ H) : candidateSiteKernel B L T H M τ C χ i t S R = 0 := by
    rw [candidateSiteKernel_factor_sum χ i t hit]
    apply sum_eq_zero
    intro ab hab
    have he := (mem_filter.mp hab).2
    have hlag := he.2.1
    change H < t.val-i.val at hlag
    omega
  rcases lt_trichotomy i t with hit | rfl | hti
  · apply hf i t hit S R
    simpa only [Nat.dist_eq_sub_of_le hit.le] using hshort
  · exact candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _
  · rw [candidateSiteKernel_symm]
    apply hf t i hti R S
    simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hshort

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LatentRowSquareMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated row estimate in the finite sampling notation -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem independentPrimePair_expectation (B : ℕ) (F : Finset ℕ → Finset ℕ → ℝ) :
    finiteExpectation (independentPrimeSetMass B) (fun S =>
      finiteExpectation (independentPrimeSetMass B) (fun R => F S.val R.val)) =
    ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R := by
  unfold finiteExpectation independentPrimeSetMass
  calc
    _ = ∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
          ∑ R : (auxiliaryPrimes B).powerset,
            bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R.val*F S R.val :=
      sum_coe_sort _ _
    _ = _ := by
      apply sum_congr rfl
      intro S _
      rw [sum_coe_sort (auxiliaryPrimes B).powerset
        (fun R => bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R),mul_sum]
      apply sum_congr rfl
      intro R _
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_WeightedCandidateKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact latent candidate kernel with a product-dependent cutoff -/

namespace JointDickman
open Finset

open Classical in
theorem candidateSiteKernel_product_weight {B L T H M V : ℕ} {τ C : ℝ}
    (hB : 1 < B) (hT : 0 < T) (hV : ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V)
    (i t : Fin M) (hit : i < t) (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    (q : ℕ → ℕ → ℝ)
    {S R : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C
      (fun e => candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
        q (candidateHigh e) (candidateLow e)) i t S R =
      independentRootMean B L τ C*regularRemainderKernel B L τ C
        (weightedCandidateRetained B L (t.val-i.val) τ C T V q) S R := by
  rw [candidateSiteKernel_fair_sum hB _ i t hit hS hR]
  unfold regularRemainderKernel weightedCandidateRetained candidateRetainedWeight
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  have he := regularCandidateScalar_eq_sum (L := L) (τ := τ) (C := C) (by omega : 0 < B) hT hV (A := A) (D := D) hit hH hjT
  change (if BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) then
    regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) ((i,t),(A,D)) else 0) = _ at he
  by_cases ha : RegularPrimeSet B L τ C A
  all_goals by_cases hd : RegularPrimeSet B L τ C D
  all_goals by_cases hs : RegularPrimeSet B L τ C (S \ A)
  all_goals by_cases hr : RegularPrimeSet B L τ C (R \ D)
  all_goals simp only [ha,hd,hs,hr,and_self,and_true,and_false,
    ite_true, if_true,ite_false, if_false,mul_zero,zero_mul]
  by_cases had : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
  · rw [ite_eq_left had] at he
    rw [ite_eq_left had,← mul_sum,← he]
    change _ = independentRootMean B L τ C*
      (subsetRetentionMass S A*subsetRetentionMass R D*
        (B*(regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
          candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) ((i,t),(A,D)))*
          q (candidateHigh ((i,t),(A,D))) (candidateLow ((i,t),(A,D)))))
    ring
  · rw [ite_eq_right had] at he
    rw [ite_eq_right had,← mul_sum,← he]
    simp only [mul_zero,zero_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCandidateComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform removal errors with the actual bounded counting restriction -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem weightedCandidateRetained_bounds (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (q : ℕ → ℕ → ℝ) (hq : ∀ a b, 0 ≤ q a b ∧ q a b ≤ 1) (A D : Finset ℕ) :
    0 ≤ weightedCandidateRetained B L j τ C T V q A D ∧
      weightedCandidateRetained B L j τ C T V q A D ≤ candidateRetainedWeight B L j τ C T V A D := by
  have hf := (candidateRetainedWeight_bounds B L j τ C T V A D).1
  exact ⟨mul_nonneg hf (hq _ _).1,
    (mul_le_mul_of_nonneg_left (hq _ _).2 hf).trans_eq (mul_one _)⟩

open Classical in
theorem weighted_candidate_remainder_removal
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → ∀ j T U V : ℕ,
          0 < T → Real.log T ≤ (B : ℝ)/10 → (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          ∀ q : ℕ → ℕ → ℝ, (∀ a b, 0 ≤ q a b ∧ q a b ≤ 1) →
          ∀ g h : Finset ℕ → ℝ, (∀ S, |g S| ≤ 1) → (∀ R, |h R| ≤ 1) →
          |subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B)
              (weightedCandidateRetained B L j τ C T V q))-
            subsetKernelBilinear B g h (regularRemainderKernel B L τ C
              (weightedCandidateRetained B L j τ C T V q))| ≤
          K*(ε B+Real.exp (-(1/10 : ℝ)*C))*
            amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
  obtain ⟨K,hK,hloss⟩ := remainderKernel_regularity_estimate hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss,eventually_ge_atTop 30] with B hb hB
  intro C hC j T U V hT hlog hU q hq g h hg hh
  have hbnd := weightedCandidateRetained_bounds B L j τ C T V q hq
  have he := hb C hC (weightedCandidateRetained B L j τ C T V q)
    (fun A _ D _ => (hbnd A D).1)
    (fun A _ D _ hne => candidateRetainedWeight_support hB hT hlog
      (left_ne_zero_of_mul hne)) g h hg hh
  have hmass : (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*
      weightedCandidateRetained B L j τ C T V q A D) ≤
      amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
    apply le_trans _ (candidateRetainedWeight_positive_mass_le B L j T U V τ C hU)
    apply sum_le_sum
    intro A hA
    apply sum_le_sum
    intro D hD
    have hp : ∀ p ∈ auxiliaryPrimes B, 0 ≤ (1/2 : ℝ)/p ∧ (1/2 : ℝ)/p ≤ 1 := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
      exact ⟨by positivity,(div_le_one (by linarith)).mpr (by linarith)⟩
    exact mul_le_mul_of_nonneg_left (hbnd A D).2
      (mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hA) hp)
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hD) hp))
  exact he.trans (mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hK.le (add_nonneg (hε0 B) (Real.exp_pos _).le)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCandidateMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual smooth latent candidate mean compared with its arithmetic sum -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem weightedCandidateMean_eq_remainderMean {B L T H M V : ℕ} {τ C : ℝ}
    (hB : 1 < B) (hT : 0 < T) (hV : ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V)
    (i t : Fin M) (hit : i < t) (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    (q : ℕ → ℕ → ℝ) (g h : Finset ℕ → ℝ) :
    subsetKernelBilinear B g h
      (candidateSiteKernel B L T H M τ C
        (fun e => candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
          q (candidateHigh e) (candidateLow e)) i t) =
    independentRootMean B L τ C*subsetKernelBilinear B g h
      (regularRemainderKernel B L τ C (weightedCandidateRetained B L (t.val-i.val) τ C T V q)) := by
  unfold subsetKernelBilinear
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro S hS
  apply sum_congr rfl
  intro R hR
  rw [candidateSiteKernel_product_weight hB hT hV i t hit hH hjT q
    (mem_powerset.mp hS) (mem_powerset.mp hR)]
  ring

open Classical in
theorem weighted_candidate_arithmetic_comparison
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ Kr Kc : ℝ, 0 < Kr ∧ 0 < Kc ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ er ec : ℕ → ℝ, (∀ B, 0 ≤ er B) ∧ (∀ B, 0 ≤ ec B) ∧
        Tendsto er atTop (𝓝 0) ∧ Tendsto ec atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V : ℕ),
          0 ≤ C → 0 < T → Real.log T ≤ (B : ℝ)/10 →
          (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ i t : Fin M, i < t → H < t.val-i.val → t.val-i.val < T →
          ∀ q : ℕ → ℕ → ℝ, (∀ a b, 0 ≤ q a b ∧ q a b ≤ 1) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
              (subsetSiteTest (auxiliaryPrimes B) h)
              (candidateSiteKernel B L T H M τ C
                (fun e => candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
          q (candidateHigh e) (candidateLow e)) i t)-
            independentRootMean B L τ C*weightedAmplificationArithmeticSum B (t.val-i.val) T U V q h g| ≤
          independentRootMean B L τ C*
            (Kr*(er B+Real.exp (-(1/10 : ℝ)*C))*
                amplificationArithmeticSum B (t.val-i.val) T U V (fun _ => 1) (fun _ => 1)+
              ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              Kc/T*singularFactor 24 (t.val-i.val)*(ec B+Real.exp (-(1/10 : ℝ)*C))) := by
  obtain ⟨Kr,hKr,hrem⟩ := weighted_candidate_remainder_removal hM
  obtain ⟨Kc,hKc,hcoef⟩ := weighted_candidate_coefficient_removal_jd hFord hM
  refine ⟨Kr,Kc,hKr,hKc,?_⟩
  intro L τ hL hτ
  obtain ⟨er,her0,her,hrem⟩ := hrem L τ hL hτ
  obtain ⟨ec,hec0,hec,hcoef⟩ := hcoef L τ hL hτ
  refine ⟨er,ec,her0,hec0,her,hec,?_⟩
  filter_upwards [hrem,hcoef,eventually_ge_atTop 30] with B hr hc hB
  intro C T H M U V hC hT hlog hU hV hdyU hdyV i t hit hH hjT q hq g h hg hh
  have hB1 : 1 < B := by omega
  have hj : 0 < t.val-i.val := Nat.sub_pos_of_lt hit
  have her := hr C hC (t.val-i.val) T U V hT hlog hU
    q hq (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
    (fun S => hg _) (fun R => hh _)
  have hec := hc T hT hlog C (t.val-i.val) U V hC hj hU hdyU hdyV q (fun a b => by rw [abs_of_nonneg (hq a b).1]; exact (hq a b).2) g h hg hh
  rw [weightedCandidateMean_eq_remainderMean hB1 hT hV i t hit hH hjT q]
  rw [← mul_sub,abs_mul,abs_of_nonneg (independentRootMean_nonneg B L τ C)]
  apply mul_le_mul_of_nonneg_left _ (independentRootMean_nonneg B L τ C)
  have hs := abs_sub_le
    (subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h)
      (regularRemainderKernel B L τ C (weightedCandidateRetained B L (t.val-i.val) τ C T V q)))
    (subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h)
      (retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L (t.val-i.val) τ C T V q)))
    (weightedAmplificationArithmeticSum B (t.val-i.val) T U V q h g)
  rw [abs_sub_comm] at her
  exact hs.trans (by linarith only [her,hec])

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual candidate cutoff and its ramped arithmetic counterpart -/
namespace JointDickman
open Finset

theorem rampedProductCutoff_bounds {δ : ℝ} (hδ : 0 < δ) (T j : ℕ) (σ : ℝ) (a b : ℕ) :
    0 ≤ rampedProductCutoff T j δ σ a b ∧ rampedProductCutoff T j δ σ a b ≤ 1 :=
  countingRamp_bounds hδ σ _

open Classical in
theorem candidateSiteKernel_pair_cutoff_congr {B L T H M : ℕ} {τ C : ℝ}
    (χ ψ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    (hχ : ∀ A D, χ ((i,t),(A,D)) = ψ ((i,t),(A,D))) (S R : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      candidateSiteKernel B L T H M τ C ψ i t S R := by
  rw [candidateSiteKernel_factor_sum χ i t hit,candidateSiteKernel_factor_sum ψ i t hit]
  apply sum_congr rfl
  intro ab _
  unfold candidateCoefficientFactor
  rw [hχ]

theorem rampedCandidateCutoff_pair {M : ℕ} (B T : ℕ) (δ σ : ℝ)
    (i t : Fin M) (A D : Finset ℕ) :
    rampedCandidateCutoff B T δ σ ((i,t),(A,D)) =
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) ((i,t),(A,D))*
        rampedProductCutoff T (t.val-i.val) δ σ
          (candidateHigh ((i,t),(A,D))) (candidateLow ((i,t),(A,D))) := rfl

open Classical in
theorem rampedArithmetic_eq_weighted (B j T U V : ℕ) (hj : 0 < j) (δ σ : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    rampedAmplificationArithmeticSum B j T U V δ σ g h =
      weightedAmplificationArithmeticSum B j T U V (rampedProductCutoff T j δ σ) g h := by
  unfold rampedAmplificationArithmeticSum weightedAmplificationArithmeticSum
  congr 1
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  by_cases he : a = b+j*c
  · have hq : (a-b)/j = c := by rw [he,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left c hj]
    simp only [rampedProductCutoff,hq]
  · simp only [amplificationArithmeticTerm,ite_eq_right he,zero_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampedCandidateMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counting-ramp candidate mean with all arithmetic removal errors -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem ramped_candidate_arithmetic_comparison
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ Kr Kc : ℝ, 0 < Kr ∧ 0 < Kc ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ er ec : ℕ → ℝ, (∀ B, 0 ≤ er B) ∧ (∀ B, 0 ≤ ec B) ∧
        Tendsto er atTop (𝓝 0) ∧ Tendsto ec atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V : ℕ),
          0 ≤ C → 0 < T → Real.log T ≤ (B : ℝ)/10 →
          (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ i t : Fin M, i < t → H < t.val-i.val → t.val-i.val < T →
          ∀ δ σ : ℝ, 0 < δ →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
              (subsetSiteTest (auxiliaryPrimes B) h)
              (candidateSiteKernel B L T H M τ C
                (rampedCandidateCutoff B T δ σ) i t)-
            independentRootMean B L τ C*rampedAmplificationArithmeticSum B (t.val-i.val) T U V δ σ h g| ≤
          independentRootMean B L τ C*
            (Kr*(er B+Real.exp (-(1/10 : ℝ)*C))*
                amplificationArithmeticSum B (t.val-i.val) T U V (fun _ => 1) (fun _ => 1)+
              ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              Kc/T*singularFactor 24 (t.val-i.val)*(ec B+Real.exp (-(1/10 : ℝ)*C))) := by
  obtain ⟨Kr,Kc,hKr,hKc,hcomp⟩ := weighted_candidate_arithmetic_comparison hFord hM
  refine ⟨Kr,Kc,hKr,hKc,?_⟩
  intro L τ hL hτ
  obtain ⟨er,ec,her0,hec0,her,hec,hcomp⟩ := hcomp L τ hL hτ
  refine ⟨er,ec,her0,hec0,her,hec,?_⟩
  filter_upwards [hcomp] with B hb
  intro C T H M U V hC hT hlog hU hV hdyU hdyV i t hit hH hjT δ σ hδ g h hg hh
  let q := rampedProductCutoff T (t.val-i.val) δ σ
  have he := hb C T H M U V hC hT hlog hU hV hdyU hdyV i t hit hH hjT
    q (rampedProductCutoff_bounds hδ T (t.val-i.val) σ) g h hg hh
  have hk : candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T δ σ) i t =
      candidateSiteKernel B L T H M τ C
        (fun e => candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
          q (candidateHigh e) (candidateLow e)) i t := by
    funext S R
    exact candidateSiteKernel_pair_cutoff_congr _ _ i t hit
      (rampedCandidateCutoff_pair B T δ σ i t) S R
  rw [← hk] at he
  have ha := rampedArithmetic_eq_weighted B (t.val-i.val) T U V (Nat.sub_pos_of_lt hit) δ σ h g
  rw [← ha] at he
  exact he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SubsetPrimeModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting a finite prime-feature model to endpoint subsets -/
namespace JointDickman
open Finset Classical

theorem subsetKernelBilinear_primeModel (B : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ) :
    subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h) (subsetPrimeModel B K) =
      ∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
        g x*h y*K x y := by
  rw [← (subsetHitEquiv (auxiliaryPrimes B)).sum_comp]
  simp_rw [← (subsetHitEquiv (auxiliaryPrimes B)).sum_comp
    (fun y => fullPrimeMass (auxiliaryPrimes B) _*fullPrimeMass (auxiliaryPrimes B) y*
      g _*h y*K _ y)]
  simp_rw [fullPrimeMass_subset]
  let F (S R : Finset ℕ) :=
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
    subsetSiteTest (auxiliaryPrimes B) g S*subsetSiteTest (auxiliaryPrimes B) h R*
    subsetPrimeModel B K S R
  change (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset, F S R) =
    ∑ S : (auxiliaryPrimes B).powerset, ∑ R : (auxiliaryPrimes B).powerset, F S.val R.val
  symm
  exact (sum_coe_sort (auxiliaryPrimes B).powerset
    (fun S => ∑ R : (auxiliaryPrimes B).powerset, F S R.val)).trans
    (sum_congr rfl (fun S _ => sum_coe_sort (auxiliaryPrimes B).powerset (F S)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetPairTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same independent endpoint tests in subset and Boolean coordinates -/
namespace JointDickman
open Finset Classical

theorem extendSubsetTest_subset (B : ℕ) (g : (auxiliaryPrimes B).powerset → ℝ)
    (S : (auxiliaryPrimes B).powerset) :
    subsetSiteTest (auxiliaryPrimes B) (extendSubsetTest B g) S.val = g S := by
  change g ((subsetHitEquiv (auxiliaryPrimes B)).symm (subsetHitEquiv (auxiliaryPrimes B) S)) = g S
  rw [Equiv.symm_apply_apply]

theorem subsetKernelBilinear_eq_expectation (B : ℕ) (g h : Finset ℕ → ℝ)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    subsetKernelBilinear B g h F =
      finiteExpectation (independentPrimeSetMass B) (fun S =>
        finiteExpectation (independentPrimeSetMass B) (fun R => F S.val R.val*g S.val*h R.val)) := by
  rw [independentPrimePair_expectation B (fun S R => F S R*g S*h R)]
  unfold subsetKernelBilinear
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro R _
  ring

theorem subsetKernelBilinear_sub (B : ℕ) (g h : Finset ℕ → ℝ)
    (F G : Finset ℕ → Finset ℕ → ℝ) :
    subsetKernelBilinear B g h (fun S R => F S R-G S R) =
      subsetKernelBilinear B g h F-subsetKernelBilinear B g h G := by
  simp only [subsetKernelBilinear,mul_sub,sum_sub_distrib]

theorem subset_pair_error_of_boolean_tests (B : ℕ) (F G : Finset ℕ → Finset ℕ → ℝ)
    {ε : ℝ}
    (hFG : ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
        (subsetSiteTest (auxiliaryPrimes B) h) F-
       subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
        (subsetSiteTest (auxiliaryPrimes B) h) G| ≤ ε)
    (g h : (auxiliaryPrimes B).powerset → ℝ)
    (hg : ∀ S, |g S| ≤ 1) (hh : ∀ S, |h S| ≤ 1) :
    |finiteExpectation (independentPrimeSetMass B) (fun S =>
      finiteExpectation (independentPrimeSetMass B)
        (fun R => (F S.val R.val-G S.val R.val)*g S*h R))| ≤ ε := by
  have hf := hFG (extendSubsetTest B g) (extendSubsetTest B h)
    (fun x => hg _) (fun x => hh _)
  rw [← subsetKernelBilinear_sub,subsetKernelBilinear_eq_expectation] at hf
  simpa only [extendSubsetTest_subset] using hf

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

theorem subsetKernelBilinear_const_mul (B : ℕ) (g h : Finset ℕ → ℝ)
    (K : Finset ℕ → Finset ℕ → ℝ) (c : ℝ) :
    subsetKernelBilinear B g h (fun S R => c*K S R) = c*subsetKernelBilinear B g h K := by
  unfold subsetKernelBilinear
  simp only [mul_sum]
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro R _
  ring

theorem countingCandidateModel_mean (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L j : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h) (countingCandidateModel P m B L j τ C c H T σ) =
    independentRootMean B L τ C*((singularSeries j/(j : ℝ))*(∑ x, ∑ y,
      fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*h x*g y*
        countingPrimeKernel P m B j c H T σ x y)) := by
  unfold countingCandidateModel
  rw [subsetKernelBilinear_const_mul,subsetKernelBilinear_primeModel]
  rw [sum_comm]
  simp only [mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCandidateComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual latent counting-ramp entry has a finite prime-feature model -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem counting_candidate_feature_comparison
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    :
    ∃ Kr Kc : ℝ, 0 < Kr ∧ 0 < Kc ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ er ec : ℕ → ℝ, (∀ B, 0 ≤ er B) ∧ (∀ B, 0 ≤ ec B) ∧
        Tendsto er atTop (𝓝 0) ∧ Tendsto ec atTop (𝓝 0) ∧
        ∀ η w δ : ℝ, 0 < η → 0 < w → 0 < δ →
        ∃ P : MvPolynomial (Fin 4) ℝ,
        ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
        (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
        ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
        ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V Q : ℕ),
          0 ≤ C → 0 < T → Real.log T ≤ (B : ℝ)/10 →
          (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q →
          ∀ i t : Fin M, i < t → H < t.val-i.val → t.val-i.val < T →
          (t.val-i.val)*Q ≤ B → η*T ≤ ((t.val-i.val : ℕ) : ℝ) →
          ∀ σ : ℝ, |σ| ≤ 3 →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          (T : ℝ)*|subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
              (subsetSiteTest (auxiliaryPrimes B) h)
              (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i t)-
            subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
              (subsetSiteTest (auxiliaryPrimes B) h)
              (countingCandidateModel P m B L (t.val-i.val) τ C c D T σ)| ≤
          independentRootMean B L τ C*
            ((T : ℝ)*(Kr*(er B+Real.exp (-(1/10 : ℝ)*C))*
                amplificationArithmeticSum B (t.val-i.val) T U V (fun _ => 1) (fun _ => 1)+
              ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              Kc/T*singularFactor 24 (t.val-i.val)*(ec B+Real.exp (-(1/10 : ℝ)*C)))+
              ε B+δ*((T : ℝ)/((t.val-i.val : ℕ) : ℝ))*singularSeries (t.val-i.val)) ∧
          ∀ x y, |countingPrimeKernel P m B (t.val-i.val) c D T σ x y| ≤ C₀ := by
  obtain ⟨Kr,Kc,hKr,hKc,hcandidate⟩ := ramped_candidate_arithmetic_comparison hFord hM
  refine ⟨Kr,Kc,hKr,hKc,?_⟩
  intro L τ hL hτ
  obtain ⟨er,ec,her0,hec0,her,hec,hcandidate⟩ := hcandidate L τ hL hτ
  refine ⟨er,ec,her0,hec0,her,hec,?_⟩
  intro η w δ hη hw hδ
  obtain ⟨P,c,hc,D,m,hm,C₀,hC₀,ε,hε,hfeature⟩ :=
    counting_arithmetic_feature_comparison_jd hSD hSW hM hMP hη hw δ hδ
  refine ⟨P,c,hc,D,m,hm,C₀,hC₀,ε,hε,?_⟩
  filter_upwards [hcandidate,hfeature] with B hb hf
  intro C T H M U V Q hC hT hlog hU hV hdyU hdyV hQ hcut i t hit hH hjT hscale hlag σ hσ g h hg hh
  let j := t.val-i.val
  have : NeZero j := ⟨Nat.ne_of_gt (Nat.sub_pos_of_lt hit)⟩
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have ha := hb C T H M U V hC hT hlog hU hV hdyU hdyV i t hit hH hjT w σ hw g h hg hh
  obtain ⟨hf,hbound⟩ := hf j Q hQ hscale hcut T hT1 hlog hlag σ hσ U V hdyU hdyV h g hh hg
  refine ⟨?_,hbound⟩
  rw [countingCandidateModel_mean]
  let A := subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
    (subsetSiteTest (auxiliaryPrimes B) h)
    (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i t)
  let R := independentRootMean B L τ C
  let S := (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
    fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*h x*g y*
      countingPrimeKernel P m B j c D T σ x y)
  let a := rampedAmplificationArithmeticSum B j T U V w σ h g
  have hR : 0 ≤ R := independentRootMean_nonneg ..
  have ht : |A-R*S| ≤ |A-R*a|+R*|a-S| := by
    have h := abs_sub_le A (R*a) (R*S)
    have he : |R*a-R*S| = R*|a-S| := by rw [← mul_sub,abs_mul,abs_of_nonneg hR]
    exact h.trans_eq (congrArg (fun z => |A-R*a|+z) he)
  calc
    _ = (T : ℝ)*|A-R*S| := rfl
    _ ≤ (T : ℝ)*|A-R*a|+R*((T : ℝ)*|a-S|) :=
      (mul_le_mul_of_nonneg_left ht hTr.le).trans_eq (by ring)
    _ ≤ (T : ℝ)*(R*(Kr*(er B+Real.exp (-(1/10 : ℝ)*C))*
                amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1)+
              ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              Kc/T*singularFactor 24 j*(ec B+Real.exp (-(1/10 : ℝ)*C))))+
        R*(ε B+δ*((T : ℝ)/j)*singularSeries j) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hTr.le) (mul_le_mul_of_nonneg_left hf hR)
    _ = _ := by dsimp only [R,j] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingErrorRate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A vanishing error profile for the counting candidate comparison -/
namespace JointDickman
open Filter
open scoped Topology

theorem countingErrorRate_nonneg {R Kr Kc Kp η : ℝ}
    (hR : 0 ≤ R) (hKr : 0 ≤ Kr) (hKc : 0 ≤ Kc) (hKp : 0 ≤ Kp) (hη : 0 ≤ η)
    {er ec ep ef : ℕ → ℝ} (her : ∀ B, 0 ≤ er B) (hec : ∀ B, 0 ≤ ec B) (B : ℕ) :
    0 ≤ countingErrorRate R Kr Kc Kp η er ec ep ef B := by
  have hg : 0 ≤ (amplificationMultiplier B : ℝ)*
      (((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg _)) (by positivity))
  unfold countingErrorRate
  exact mul_nonneg hR (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hKr (by linarith [her B])) (abs_nonneg _)) hg)
    (mul_nonneg hKc (hec B))) (abs_nonneg _))
    (mul_nonneg (div_nonneg (mul_nonneg hKr hKp) hη) (her B)))

theorem countingErrorRate_tendsto (R Kr Kc Kp η : ℝ)
    {er ec ep ef : ℕ → ℝ} (her : Tendsto er atTop (𝓝 0))
    (hec : Tendsto ec atTop (𝓝 0)) (hep : Tendsto ep atTop (𝓝 0))
    (hef : Tendsto ef atTop (𝓝 0)) :
    Tendsto (countingErrorRate R Kr Kc Kp η er ec ep ef) atTop (𝓝 0) := by
  unfold countingErrorRate
  have hp := ((her.add_const 1).const_mul Kr).mul hep.abs
  have h := ((((hp.add amplification_gcd_rate_tendsto).add (hec.const_mul Kc)).add hef.abs).add
    (her.const_mul (Kr*Kp/η))).const_mul R
  simpa only [zero_add,add_zero,zero_mul,mul_zero,abs_zero] using h

theorem countingErrorProfile_bound {R Kr Kc Kp η er ec ep ef g δ q s : ℝ}
    (hR : 0 ≤ R) (hKr : 0 ≤ Kr) (her : 0 ≤ er) (hep : 0 ≤ ep)
    (hef : 0 ≤ ef) (hg : 0 ≤ g) (hq : q ≤ 1) (hs : 1 ≤ s) :
    R*(Kr*(er+q)*(ep+(Kp/η)*s)+g+Kc*s*(ec+q)+ef+(δ/η)*s) ≤
      (R*(Kr*(er+1)*ep+g+Kc*ec+ef+(Kr*Kp/η)*er)+
        R*(Kr*Kp/η+Kc)*q+R*δ/η)*s := by
  have hpos : 0 ≤ R*(Kr*ep*(er*(s-1)+(s-q))+(g+ef)*(s-1)) := by
    apply mul_nonneg hR
    exact add_nonneg
      (mul_nonneg (mul_nonneg hKr hep)
        (add_nonneg (mul_nonneg her (by linarith)) (by linarith)))
      (mul_nonneg (add_nonneg hg hef) (by linarith))
  have he : (R*(Kr*(er+1)*ep+g+Kc*ec+ef+(Kr*Kp/η)*er)+
        R*(Kr*Kp/η+Kc)*q+R*δ/η)*s-
      R*(Kr*(er+q)*(ep+(Kp/η)*s)+g+Kc*s*(ec+q)+ef+(δ/η)*s) =
      R*(Kr*ep*(er*(s-1)+(s-q))+(g+ef)*(s-1)) := by ring
  linarith only [hpos,he]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingErrorBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collecting the arithmetic errors into a summable singular-factor profile -/
namespace JointDickman

theorem countingError_bound
    {T j η R r Kr Kc Kp er ec ep ef pa g G δ q s Sj x : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hlag : η*T ≤ j)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hKr : 0 ≤ Kr) (hKc : 0 ≤ Kc) (hKp : 0 ≤ Kp)
    (her : 0 ≤ er) (hec : 0 ≤ ec) (hG : 0 ≤ G) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hδ : 0 ≤ δ) (hs : 1 ≤ s) (hSj : 0 ≤ Sj) (hSjs : Sj ≤ s)
    (hg : T*g ≤ G) (hp : T*pa ≤ ep+Kp*(T/j)*Sj)
    (hx : T*x ≤ r*(T*(Kr*(er+q)*pa+g+Kc/T*s*(ec+q))+ef+δ*(T/j)*Sj)) :
    T*x ≤ (R*(Kr*(er+1)*|ep|+G+Kc*ec+|ef|+(Kr*Kp/η)*er)+
      R*(Kr*Kp/η+Kc)*q+R*δ/η)*s := by
  have hj : 0 < j := (mul_pos hη hT).trans_le hlag
  have hR : 0 ≤ R := hr.trans hrR
  have hratio : T/j ≤ 1/η := (div_le_div_iff₀ hj hη).mpr (by nlinarith only [hlag])
  have hSJ : (T/j)*Sj ≤ s/η :=
    (mul_le_mul hratio hSjs hSj (by positivity)).trans_eq (by ring)
  have hpa : T*pa ≤ |ep|+(Kp/η)*s := by
    have he := mul_le_mul_of_nonneg_left hSJ hKp
    calc
      _ ≤ ep+Kp*((T/j)*Sj) := by simpa only [mul_assoc] using hp
      _ ≤ |ep|+Kp*(s/η) := add_le_add (le_abs_self _) he
      _ = _ := by ring
  let V := Kr*(er+q)*(|ep|+(Kp/η)*s)+G+Kc*s*(ec+q)+|ef|+(δ/η)*s
  have hraw : T*(Kr*(er+q)*pa+g+Kc/T*s*(ec+q))+ef+δ*(T/j)*Sj ≤ V := by
    have he : T*(Kr*(er+q)*pa+g+Kc/T*s*(ec+q))+ef+δ*(T/j)*Sj =
        Kr*(er+q)*(T*pa)+T*g+Kc*s*(ec+q)+ef+δ*((T/j)*Sj) := by
      field_simp
    rw [he]
    dsimp only [V]
    have hδS := mul_le_mul_of_nonneg_left hSJ hδ
    calc
      _ ≤ Kr*(er+q)*(|ep|+(Kp/η)*s)+G+Kc*s*(ec+q)+|ef|+δ*(s/η) := by
        exact add_le_add
          (add_le_add (add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hpa (mul_nonneg hKr (add_nonneg her hq0))) hg)
            le_rfl) (le_abs_self ef)) hδS
      _ = _ := by ring
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  calc
    T*x ≤ r*(T*(Kr*(er+q)*pa+g+Kc/T*s*(ec+q))+ef+δ*(T/j)*Sj) := hx
    _ ≤ r*V := mul_le_mul_of_nonneg_left hraw hr
    _ ≤ R*V := mul_le_mul_of_nonneg_right hrR hV
    _ ≤ _ := countingErrorProfile_bound hR hKr her (abs_nonneg _) (abs_nonneg _) hG hq hs

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCandidateApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A summable vanishing error for the actual finite-feature comparison -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem counting_candidate_approximation
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {L : ℕ} {τ η w δ : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (hη : 0 < η) (hw : 0 < w) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V Q : ℕ),
        0 ≤ C → 0 < T → T ≤ amplificationMultiplier B → Real.log T ≤ (B : ℝ)/10 →
        (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q →
        ∀ i t : Fin M, i < t → H < t.val-i.val → t.val-i.val < T →
        (t.val-i.val)*Q ≤ B → η*T ≤ ((t.val-i.val : ℕ) : ℝ) →
        ∀ σ : ℝ, |σ| ≤ 3 →
        ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
        (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
        (T : ℝ)*|subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
            (subsetSiteTest (auxiliaryPrimes B) h)
            (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i t)-
          subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
            (subsetSiteTest (auxiliaryPrimes B) h)
            (countingCandidateModel P m B L (t.val-i.val) τ C c D T σ)| ≤
          (ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ)*singularFactor 24 (t.val-i.val) ∧
        ∀ x y, |countingPrimeKernel P m B (t.val-i.val) c D T σ x y| ≤ C₀ := by
  obtain ⟨Kr,Kc,hKr,hKc,hcompare⟩ := counting_candidate_feature_comparison hFord hSD hSW hM hMP
  obtain ⟨er,ec,her0,hec0,her,hec,hcompare⟩ := hcompare L τ hL hτ
  obtain ⟨R,hR,hroot⟩ := independentRootMean_bounded hM
  obtain ⟨Kp,hKp,ep,hep,hpositive⟩ := amplification_positive_mass_bound_jd hSD hSW hM hMP hη
  let δ₀ := δ*η/R
  have hδ₀ : 0 < δ₀ := div_pos (mul_pos hδ hη) hR
  obtain ⟨P,c,hc,D,m,hm,C₀,hC₀,ef,hef,hcompare⟩ := hcompare η w δ₀ hη hw hδ₀
  let K := R*(Kr*Kp/η+Kc)
  let ε := countingErrorRate R Kr Kc Kp η er ec ep ef
  refine ⟨K,by dsimp [K] <;> positivity,P,c,hc,D,m,hm,C₀,hC₀,ε,
    countingErrorRate_nonneg hR.le hKr.le hKc.le hKp hη.le her0 hec0,
    countingErrorRate_tendsto R Kr Kc Kp η her hec hep hef,?_⟩
  filter_upwards [hcompare,hpositive,hroot] with B hb hp hr
  intro C T H M U V Q hC hT hTcap hlog hU hV hdyU hdyV hQ hcut i t hit hH hjT hscale hlag σ hσ g h hg hh
  let j := t.val-i.val
  have hj : 0 < j := Nat.sub_pos_of_lt hit
  have : NeZero j := ⟨hj.ne'⟩
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨he,hbound⟩ := hb C T H M U V Q hC hT hlog hU hV hdyU hdyV hQ hcut
    i t hit hH hjT hscale hlag σ hσ g h hg hh
  have hpa := hp j Q hQ hscale hcut T hT1 hlog hlag U V hdyU hdyV
  refine ⟨?_,hbound⟩
  have hG : 0 ≤ (amplificationMultiplier B : ℝ)*
      (((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg _)) (by positivity))
  have hgcd : (T : ℝ)*(((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))) ≤
      (amplificationMultiplier B : ℝ)*(((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hTcap)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg _)) (by positivity))
  have hq : Real.exp (-(1/10 : ℝ)*C) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he' := countingError_bound hTr hη hlag (independentRootMean_nonneg B L τ C)
    (hr L τ C) hKr.le hKc.le hKp (her0 B) (hec0 B) hG (Real.exp_pos _).le hq hδ₀.le
    (singularFactor_one_le (by norm_num) j) (singularSeries_bounds hMP j).1
    (singularSeries_le_singularFactor hMP hj) hgcd hpa he
  have hd : R*δ₀/η = δ := by dsimp [δ₀]; field_simp
  simpa only [hd,ε,countingErrorRate,K,j] using he'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSiteModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SitePairTestSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the two-endpoint tests needed by sampling -/
namespace JointDickman
open Finset PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

theorem siteTestMean_le_pair_sum (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (E : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, E i i a a = 0) (r : ι → ι → ℝ) (hrdiag : ∀ i, 0 ≤ r i i)
    (hpair : ∀ i j, i ≠ j → ∀ g h : A → ℝ,
      (∀ a, |g a| ≤ 1) → (∀ b, |h b| ≤ 1) →
      finiteExpectation (p i) (fun a => finiteExpectation (p j)
        (fun b => E i j a b*g a*h b)) ≤ r i j)
    (g h : ι → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1) (hh : ∀ i a, |h i a| ≤ 1) :
    siteTestMean p E g h ≤ ∑ i, ∑ j, r i j := by
  unfold siteTestMean
  rw [finiteExpectation_sum]
  apply sum_le_sum
  intro i _
  rw [finiteExpectation_sum]
  apply sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    simp only [hdiag,zero_mul,finiteExpectation,mul_zero,sum_const_zero]
    exact hrdiag i
  · exact (siteProduct_expectation_two p hpone hij
      (fun a b => E i j a b*g i a*h j b)).trans_le
      (hpair i j hij (g i) (h j) (hg i) (hh j))

theorem siteTestMean_le_of_pair_rows (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (E : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, E i i a a = 0) (r : ι → ι → ℝ) (hrdiag : ∀ i, 0 ≤ r i i)
    (hpair : ∀ i j, i ≠ j → ∀ g h : A → ℝ,
      (∀ a, |g a| ≤ 1) → (∀ b, |h b| ≤ 1) →
      finiteExpectation (p i) (fun a => finiteExpectation (p j)
        (fun b => E i j a b*g a*h b)) ≤ r i j)
    {e : ℝ} (hr : ∀ i, (∑ j, r i j) ≤ e)
    (g h : ι → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1) (hh : ∀ i a, |h i a| ≤ 1) :
    siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e :=
  (siteTestMean_le_pair_sum p hpone E hdiag r hrdiag hpair g h hg hh).trans
    ((sum_le_sum (fun i _ => hr i)).trans_eq (by simp))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSiteTest
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The block test estimate for the actual counting-feature error -/
namespace JointDickman
open Finset Classical PublishedInputs

theorem finiteExpectation_swap {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (F : A → B → ℝ) :
    finiteExpectation p (fun a => finiteExpectation q (F a)) =
      finiteExpectation q (fun b => finiteExpectation p (fun a => F a b)) := by
  unfold finiteExpectation
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

theorem countingSiteError_symm (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    countingSiteError P m B L T H M τ C w c D σ i k a b =
      countingSiteError P m B L T H M τ C w c D σ k i b a := by
  unfold countingSiteError latentPrimeSiteKernel
  rw [candidateSiteKernel_symm,countingSiteModel_symm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSiteTestBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized pair comparison gives the full block test estimate -/
namespace JointDickman
open Finset Classical PublishedInputs

theorem countingSiteError_pair_bound
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C w : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (σ r : ℝ) (hT : 0 < T) (hr : 0 ≤ r)
    (happrox : ∀ i k : Fin M, i < k → H < k.val-i.val → k.val-i.val < T →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      (T : ℝ)*|subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
          (subsetSiteTest (auxiliaryPrimes B) h)
          (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i k)-
        subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
          (subsetSiteTest (auxiliaryPrimes B) h)
          (countingCandidateModel P m B L (k.val-i.val) τ C c D T σ)| ≤
        r*singularFactor 24 (k.val-i.val))
    (i k : Fin M) (g h : (auxiliaryPrimes B).powerset → ℝ)
    (hg : ∀ a, |g a| ≤ 1) (hh : ∀ b, |h b| ≤ 1) :
    |finiteExpectation (independentPrimeSetMass B) (fun a =>
      finiteExpectation (independentPrimeSetMass B) (fun b =>
        countingSiteError P m B L T H M τ C w c D σ i k a b*g a*h b))| ≤ lagEnvelope T r i k := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hf (i k : Fin M) (hik : i < k) (g h : (auxiliaryPrimes B).powerset → ℝ)
      (hg : ∀ a, |g a| ≤ 1) (hh : ∀ b, |h b| ≤ 1) :
      |finiteExpectation (independentPrimeSetMass B) (fun a =>
        finiteExpectation (independentPrimeSetMass B) (fun b =>
          countingSiteError P m B L T H M τ C w c D σ i k a b*g a*h b))| ≤ lagEnvelope T r i k := by
    by_cases ha : H < k.val-i.val ∧ k.val-i.val < T
    · have hp := subset_pair_error_of_boolean_tests B
        (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i k)
        (countingCandidateModel P m B L (k.val-i.val) τ C c D T σ)
        (fun g h hg hh => (le_div_iff₀ hTr).mpr (by
          simpa only [mul_comm] using happrox i k hik ha.1 ha.2 g h hg hh)) g h hg hh
      have he : lagEnvelope T r i k = (r*singularFactor 24 (k.val-i.val))/(T : ℝ) := by
        rw [lagEnvelope,ite_eq_left ⟨ne_of_lt hik,by simpa [Nat.dist_eq_sub_of_le hik.le] using ha.2⟩,
          Nat.dist_eq_sub_of_le hik.le]
        ring
      rw [he]
      simpa only [countingSiteError,latentPrimeSiteKernel,countingSiteModel,hik,ite_true, if_true,ha,and_self] using hp
    · have hz (a b : (auxiliaryPrimes B).powerset) :
          countingSiteError P m B L T H M τ C w c D σ i k a b = 0 := by
        have hzero : candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i k a.val b.val = 0 := by
          by_cases hs : k.val-i.val ≤ H
          · exact candidateSiteKernel_zero_of_short _ i k _ _ (by
              simpa only [Nat.dist_eq_sub_of_le hik.le] using hs)
          · have hfar : T ≤ k.val-i.val := by omega
            exact candidateSiteKernel_zero_of_far _ i k _ _ (by
              simpa only [Nat.dist_eq_sub_of_le hik.le] using hfar)
        simp only [countingSiteError,latentPrimeSiteKernel,hzero,countingSiteModel,hik,ite_true, if_true,ha,ite_false, if_false,sub_self]
      simp only [hz,zero_mul,finiteExpectation,mul_zero,sum_const_zero,abs_zero]
      exact lagEnvelope_nonneg T hr i k
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hf i k hik g h hg hh
  · simp only [countingSiteError,latentPrimeSiteKernel,candidateSiteKernel_diag,countingSiteModel_diag,
      sub_self,zero_mul,finiteExpectation,mul_zero,sum_const_zero,abs_zero,lagEnvelope,
      ne_eq,not_true_eq_false,false_and,ite_false, if_false,le_refl]
  · have he : finiteExpectation (independentPrimeSetMass B) (fun a =>
        finiteExpectation (independentPrimeSetMass B) (fun b =>
          countingSiteError P m B L T H M τ C w c D σ i k a b*g a*h b)) =
        finiteExpectation (independentPrimeSetMass B) (fun b =>
          finiteExpectation (independentPrimeSetMass B) (fun a =>
            countingSiteError P m B L T H M τ C w c D σ k i b a*h b*g a)) := by
      rw [finiteExpectation_swap]
      apply congrArg (finiteExpectation (independentPrimeSetMass B))
      funext b
      apply congrArg (finiteExpectation (independentPrimeSetMass B))
      funext a
      rw [countingSiteError_symm]
      ring
    rw [he]
    simpa only [lagEnvelope,Nat.dist_comm,ne_comm] using hf k i hki h g hh hg

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LagEnvelopeTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A singular-factor pair bound gives the sampling fixed-test bound -/
namespace JointDickman
open Finset PublishedInputs

variable {M T : ℕ} {A : Type*} [Fintype A]

theorem siteTestMean_le_lag_envelope (hT : 0 < T) {r : ℝ} (hr : 0 ≤ r)
    (p : Fin M → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1)
    (E : Fin M → Fin M → A → A → ℝ) (hdiag : ∀ i a, E i i a a = 0)
    (hpair : ∀ i j, i ≠ j → ∀ g h : A → ℝ,
      (∀ a, |g a| ≤ 1) → (∀ b, |h b| ≤ 1) →
      |finiteExpectation (p i) (fun a => finiteExpectation (p j)
        (fun b => E i j a b*g a*h b))| ≤ lagEnvelope T r i j)
    (g h : Fin M → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1) (hh : ∀ i a, |h i a| ≤ 1) :
    siteTestMean p E g h ≤ (M : ℝ)*(2*r*Real.exp 24) := by
  simpa only [Fintype.card_fin] using siteTestMean_le_of_pair_rows p hpone E hdiag (lagEnvelope T r)
    (fun i => lagEnvelope_nonneg T hr i i)
    (fun i j hij g h hg hh => (le_abs_self _).trans (hpair i j hij g h hg hh))
    (fun i => lagEnvelope_row_sum hT hr i) g h hg hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingBlockTest
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed-test estimate for the actual latent counting graph -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_block_test_jd_oai
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) {L : ℕ} {τ η w δ : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (hη : 0 < η) (hw : 0 < w) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V Q : ℕ),
        0 ≤ C → 0 < T → T ≤ amplificationMultiplier B → Real.log T ≤ (B : ℝ)/10 →
        (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → T*Q ≤ B → η*T ≤ H → T ≤ M →
        ∀ σ : ℝ, |σ| ≤ 3 →
        (∀ j : ℕ, H < j → j < T →
          ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀) ∧
        (∀ g h : Fin M → (auxiliaryPrimes B).powerset → ℝ,
          (∀ i a, |g i a| ≤ 1) → (∀ i a, |h i a| ≤ 1) →
          siteTestMean (fun _ : Fin M => independentPrimeSetMass B)
            (countingSiteError P m B L T H M τ C w c D σ) g h ≤
            (M : ℝ)*(2*(ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ)*Real.exp 24)) := by
  obtain ⟨K,hK,P,c,hc,D,m,hm,C₀,hC₀,ε,hε0,hε,hcomp⟩ :=
    counting_candidate_approximation hFord hSD hSW hM hMP hL hτ hη hw hδ
  refine ⟨K,hK,P,c,hc,D,m,hm,C₀,hC₀,ε,hε0,hε,?_⟩
  filter_upwards [hcomp] with B hb
  intro C T H M U V Q hC hT hTcap hlog hU hV hdyU hdyV hQ hcut hscale hH hTM σ hσ
  have hMpos : 0 < M := hT.trans_le hTM
  have hepsB : 0 ≤ ε B := hε0 B
  have hpair (i k : Fin M) (hik : i < k) (hiH : H < k.val-i.val) (hkT : k.val-i.val < T) :=
    hb C T H M U V Q hC hT hTcap hlog hU hV hdyU hdyV hQ hcut i k hik hiH hkT
      ((Nat.mul_le_mul_right Q hkT.le).trans hscale)
      (hH.trans (by exact_mod_cast hiH.le)) σ hσ
  constructor
  · intro j hjH hjT x y
    let i : Fin M := ⟨0,hMpos⟩
    let k : Fin M := ⟨j,hjT.trans_le hTM⟩
    have hik : i < k := by change (0 : ℕ) < j; omega
    have he := (hpair i k hik (by simpa only [i,k,Nat.sub_zero] using hjH)
      (by simpa only [i,k,Nat.sub_zero] using hjT) (fun _ => 0) (fun _ => 0)
      (by simp) (by simp)).2 x y
    simpa only [i,k,Nat.sub_zero] using he
  · intro g h hg hh
    apply siteTestMean_le_lag_envelope hT
      (show 0 ≤ ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ by positivity)
      (fun _ : Fin M => independentPrimeSetMass B) (fun _ => independentPrimeSetMass_sum B)
      (countingSiteError P m B L T H M τ C w c D σ)
    · intro i a
      simp only [countingSiteError,latentPrimeSiteKernel,candidateSiteKernel_diag,countingSiteModel_diag,sub_self]
    · intro i k _ f h hf hh
      exact countingSiteError_pair_bound P m B L T H M τ C w c D σ
        (ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ) hT (by positivity)
        (fun i k hik hiH hkT f h hf hh => (hpair i k hik hiH hkT f h hf hh).1)
        i k f h hf hh
    · exact hg
    · exact hh

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.counting_block_test_jd_oai := @OAI.JointDickman.counting_block_test_jd_oai
