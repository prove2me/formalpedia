-- Prove2me | solution 1 for OAI.JointDickman.positive_blocks_of_graph_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:49:43.846886+00:00
-- url     : https://prove2.me/submissions/f7fc172b-22b8-472f-b2b3-0141bc031aaf

import Mathlib
import Definitions.Def_OAIQ083J003

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveSingleDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-form Euler product at the roughness cutoff -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughSieveTheta_bounds (P p : ℕ) :
    0 ≤ roughSieveTheta P p ∧ roughSieveTheta P p ≤ 1 := by
  unfold roughSieveTheta
  split_ifs <;> norm_num

theorem roughSieveRate_bounds (P p : ℕ) (hp : p.Prime) :
    0 ≤ roughSieveRate P p ∧ roughSieveRate P p ≤ 1 / (p : ℝ) ∧
      roughSieveRate P p ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hθ := roughSieveTheta_bounds P p
  have hle : roughSieveRate P p ≤ 1 / (p : ℝ) := by
    unfold roughSieveRate
    exact div_le_div_of_nonneg_right (by linarith) hp0.le
  exact ⟨div_nonneg (by linarith) hp0.le, hle,
    hle.trans ((div_le_one hp0).mpr hp1)⟩

theorem roughSieveRate_sum {P Z : ℕ} (hPZ : P ≤ Z) :
    (∑ p ∈ Nat.primesLE Z, roughSieveRate P p) = (1 / 2 : ℝ) *
      ((∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ)) + (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ))) := by
  classical
  have hfilter : (Nat.primesLE Z).filter (fun p => p ≤ P) = Nat.primesLE P := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hp⟩, hle⟩
      exact ⟨hle, hp⟩
    · rintro ⟨hle, hp⟩
      exact ⟨⟨hle.trans hPZ, hp⟩, hle⟩
  have heq (p : ℕ) : roughSieveRate P p = (1 / 2 : ℝ) * (1 / (p : ℝ)) +
      (1 / 2 : ℝ) * (if p ≤ P then 1 / (p : ℝ) else 0) := by
    unfold roughSieveRate roughSieveTheta
    split_ifs <;> ring
  simp_rw [heq]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter, hfilter]
  ring

theorem roughSieveRate_removed_le (P Z : ℕ) :
    (∑ p ∈ Nat.primesLE Z, roughSieveRate P p) ≤
      (∑ p ∈ sievePrimes Z, roughSieveRate P p) + 6 := by
  classical
  let S := (Nat.primesLE Z).filter (fun p => ¬6 ≤ p)
  have hcard : S.card ≤ 6 := by
    apply le_trans (card_le_card (show S ⊆ range 6 from fun p hp =>
      mem_range.mpr (Nat.lt_of_not_ge (mem_filter.mp hp).2)))
    simp
  have hsum : (∑ p ∈ S, roughSieveRate P p) ≤ 6 := by
    calc
      _ ≤ ∑ _p ∈ S, (1 : ℝ) := sum_le_sum (fun p hp =>
        (roughSieveRate_bounds P p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2).2.2)
      _ = S.card := by simp
      _ ≤ 6 := by exact_mod_cast hcard
  have heq := sum_filter_add_sum_filter_not (Nat.primesLE Z) (fun p => 6 ≤ p)
    (roughSieveRate P)
  change (∑ p ∈ sievePrimes Z, roughSieveRate P p) + (∑ p ∈ S, roughSieveRate P p) = _ at heq
  linarith

/-- The square of the one-form density has exactly the required two
logarithms in its denominator; bounded primes have already been removed. -/
theorem roughSieveDensity_log_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ P Z : ℕ, 2 ≤ P → P ≤ Z →
      roughSieveDensity P Z ^ 2 * Real.log P * Real.log Z ≤ C := by
  obtain ⟨M, A, hA, hMertens⟩ := hM
  let K := M - A / Real.log 2
  have hlow (N : ℕ) (hN : 2 ≤ N) :
      Real.log (Real.log N) + K ≤ ∑ p ∈ Nat.primesLE N, 1 / (p : ℝ) := by
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h := (abs_le.mp (hMertens N hN2)).1
    rw [Nat.floor_natCast, ← primesLE_eq_filter] at h
    have hdiv := div_le_div_of_nonneg_left hA (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (Real.log_le_log (by norm_num) hN2)
    dsimp [K]
    linarith
  refine ⟨Real.exp (12 - 2 * K), Real.exp_pos _, ?_⟩
  intro P Z hP hPZ
  have hZ : 2 ≤ Z := hP.trans hPZ
  have hlP : 0 < Real.log P := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hlZ : 0 < Real.log Z := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  let S := ∑ p ∈ sievePrimes Z, roughSieveRate P p
  have hS : (1 / 2 : ℝ) * (Real.log (Real.log P) + Real.log (Real.log Z)) + K - 6 ≤ S := by
    have hrem := roughSieveRate_removed_le P Z
    rw [roughSieveRate_sum hPZ] at hrem
    dsimp [S]
    linarith [hlow P hP, hlow Z hZ]
  have hd0 : 0 ≤ roughSieveDensity P Z := prod_nonneg (fun p hp =>
    sub_nonneg.mpr (roughSieveRate_bounds P p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2).2.2)
  have hd : roughSieveDensity P Z ≤ Real.exp (-S) := by
    calc
      _ ≤ ∏ p ∈ sievePrimes Z, Real.exp (-roughSieveRate P p) := Finset.prod_le_prod
        (fun p hp => sub_nonneg.mpr
          (roughSieveRate_bounds P p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2).2.2)
        (fun p _ => Real.one_sub_le_exp_neg _)
      _ = Real.exp (-S) := by rw [← Real.exp_sum, sum_neg_distrib]
  calc
    _ ≤ Real.exp (-S) ^ 2 * Real.log P * Real.log Z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hd0 hd 2) hlP.le) hlZ.le
    _ = Real.exp (-2 * S + Real.log (Real.log P) + Real.log (Real.log Z)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hlP, Real.exp_log hlZ]
      have he : Real.exp (-S) ^ 2 = Real.exp (-2 * S) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

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

theorem coefficientScale_sq_eq {B : ℕ} (hB : 1 < B) :
    coefficientScale B ^ 2 = (B : ℝ) * Real.log (auxiliaryCutoff B) := by
  have hR := auxiliaryRatio_pos hB
  have hpow : (auxiliaryRatio B ^ (1 / 2 : ℝ)) ^ 2 = auxiliaryRatio B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  rw [coefficientScale, mul_pow, hpow]
  have hmul := auxiliaryRatio_mul_log hB
  nlinarith

theorem roughSieveDensity_nonneg (P Z : ℕ) : 0 ≤ roughSieveDensity P Z :=
  prod_nonneg (fun p hp => sub_nonneg.mpr
    (roughSieveRate_bounds P p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2).2.2)

theorem coefficient_sieve_density_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z : ℕ, 1 < B → auxiliaryCutoff B ≤ Z →
      δ * B ≤ Real.log Z →
      coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z ≤ C := by
  obtain ⟨K, hK, hbound⟩ := roughSieveDensity_log_bound hM
  refine ⟨Real.sqrt (K / δ), Real.sqrt_pos.mpr (div_pos hK hδ), ?_⟩
  intro B Z hB hPZ hlog
  have hP : 2 ≤ auxiliaryCutoff B := by
    exact one_lt_pow₀ hB (by decide : (1000 : ℕ) ≠ 0)
  have hb := hbound (auxiliaryCutoff B) Z hP hPZ
  have hδmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (sq_nonneg (roughSieveDensity (auxiliaryCutoff B) Z))
      (Real.log_natCast_nonneg (auxiliaryCutoff B)))
  have hsq : (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) ^ 2 ≤ K / δ := by
    apply (le_div_iff₀ hδ).mpr
    rw [mul_pow, coefficientScale_sq_eq hB]
    nlinarith
  apply (sq_le_sq₀ (mul_nonneg (coefficientScale_nonneg B) (roughSieveDensity_nonneg _ _))
    (Real.sqrt_nonneg _)).mp
  rwa [Real.sq_sqrt (div_pos hK hδ).le]

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite periodic averages and coprime residue factorization

Integer averages of a function on `ZMod q` converge to its uniform residue
mean. The proof is the exact complete-block/remainder identity. The Chinese
remainder equivalence then gives factorization for fixed coprime moduli.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

theorem residue_sum_eq_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, f a) = ∑ n ∈ Finset.range q, f (n : ZMod q) := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  exact Fintype.sum_equiv (residueEquiv q) _ _ (fun _ => rfl)

/-- Complete blocks have exactly the same sum, with an unaltered final
prefix. This equality also holds when the modulus is zero. -/
theorem periodic_sum_blocks {q : ℕ} (f : ZMod q → ℂ) (k r : ℕ) :
    (∑ n ∈ Finset.range (k * q + r), f (n : ZMod q)) =
      (k : ℂ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) +
        ∑ n ∈ Finset.range r, f (n : ZMod q) := by
  have hshift (k n : ℕ) : f ((k * q + n : ℕ) : ZMod q) = f (n : ZMod q) := by
    simp
  have hblocks : ∀ k : ℕ, (∑ n ∈ Finset.range (k * q), f (n : ZMod q)) =
      (k : ℂ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
        Nat.cast_one]
      ring
  rw [Finset.sum_range_add, hblocks]
  simp only [hshift]

theorem periodic_sum_div_mod {q : ℕ} (f : ZMod q → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n : ZMod q)) =
      (N / q : ℕ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) +
        ∑ n ∈ Finset.range (N % q), f (n : ZMod q) := by
  have hsplit : N / q * q + N % q = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  simpa only [hsplit] using periodic_sum_blocks f (N / q) (N % q)

private theorem prefix_centered_bound {q r : ℕ} (hq : 0 < q) (hr : r ≤ q)
    (F : ℕ → ℂ) {M : ℝ} (hF : ∀ i < q, ‖F i‖ ≤ M) :
    ‖(∑ i ∈ Finset.range r, F i) -
      ((r : ℂ) / q) * ∑ i ∈ Finset.range q, F i‖ ≤ q * M := by
  classical
  have hprefix : (∑ i ∈ Finset.range r, F i) =
      ∑ i ∈ Finset.range q, if i < r then F i else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  have hid : (∑ i ∈ Finset.range r, F i) -
      ((r : ℂ) / q) * ∑ i ∈ Finset.range q, F i =
      ∑ i ∈ Finset.range q, ((if i < r then (1 : ℂ) else 0) - (r : ℂ) / q) * F i := by
    rw [hprefix, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [hid]
  refine (norm_sum_le _ _).trans ?_
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hquot0 : 0 ≤ (r : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hqR.le
  have hquot1 : (r : ℝ) / q ≤ 1 := (div_le_one hqR).mpr (by exact_mod_cast hr)
  calc
    _ ≤ ∑ i ∈ Finset.range q, M := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoef : ‖(if i < r then (1 : ℂ) else 0) - (r : ℂ) / q‖ ≤ 1 := by
        have hcast : (r : ℂ) / q = (((r : ℝ) / q : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast]
        split_ifs
        · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        · simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hquot0]
          exact hquot1
      rw [norm_mul]
      exact (mul_le_mul hcoef (hF i (Finset.mem_range.mp hi)) (norm_nonneg _) (by norm_num)).trans
        (by simp)
    _ = q * M := by simp

/-- The remainder error is at most one period times the uniform norm,
divided by the averaging length. -/
theorem periodicAverage_error {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    {N : ℕ} (hN : 0 < N) :
    ‖periodicAverage f N - residueMean f‖ ≤ (q : ℝ) * ‖f‖ / N := by
  have hq : 0 < q := NeZero.pos q
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : periodicAverage f N - residueMean f =
      ((∑ i ∈ Finset.range (N % q), f (i : ZMod q)) -
        ((N % q : ℕ) : ℂ) / q * ∑ i ∈ Finset.range q, f (i : ZMod q)) / N := by
    unfold periodicAverage residueMean
    rw [residue_sum_eq_range, periodic_sum_div_mod]
    have hdecomp : (N : ℂ) = ((N / q : ℕ) : ℂ) * q + (N % q : ℕ) := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm :
        N = N / q * q + N % q)
    field_simp
    linear_combination -(∑ i ∈ Finset.range q, f (i : ZMod q)) * hdecomp
  rw [hid, norm_div]
  have hprefix := prefix_centered_bound hq (Nat.mod_lt N hq).le
    (fun i => f (i : ZMod q)) (fun i _ => norm_le_pi_norm f _)
  have hnormN : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hnormN]
  exact div_le_div_of_nonneg_right hprefix (Nat.cast_nonneg _)

theorem periodicAverage_tendsto {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    Tendsto (periodicAverage f) atTop (𝓝 (residueMean f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun N : ℕ => (q : ℝ) * ‖f‖ / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((eventually_gt_atTop 0).mono (fun N hN => periodicAverage_error f hN)) hlim

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicNonnegative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodic interval counts with a sparse error

For a nonnegative periodic weight, the error is bounded by its total mass
in one period. This retains the number of allowed residues in sieve errors.
-/

namespace JointDickman

open Finset

private theorem real_periodic_sum_div_mod {q : ℕ} (f : ZMod q → ℝ) (N : ℕ) :
    (∑ n ∈ range N, f n) =
      (N / q : ℕ) * (∑ n ∈ range q, f n) + ∑ n ∈ range (N % q), f n := by
  have h := periodic_sum_div_mod (fun a => (f a : ℂ)) N
  exact_mod_cast h

/-- A prefix costs at most the mass of one complete period. -/
theorem nonnegative_periodic_prefix_error {q : ℕ} (hq : 0 < q)
    (f : ZMod q → ℝ) (hf : ∀ a, 0 ≤ f a) (N : ℕ) :
    |(∑ n ∈ range N, f n) - (N : ℝ) / q * ∑ n ∈ range q, f n| ≤
      ∑ n ∈ range q, f n := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : N % q < q := Nat.mod_lt N hq
  have hrR : ((N % q : ℕ) : ℝ) ≤ q := by exact_mod_cast hr.le
  have hfull : 0 ≤ ∑ n ∈ range q, f n := sum_nonneg (fun n _ => hf n)
  have hpart : 0 ≤ ∑ n ∈ range (N % q), f n := sum_nonneg (fun n _ => hf n)
  have hle : (∑ n ∈ range (N % q), f n) ≤ ∑ n ∈ range q, f n :=
    sum_le_sum_of_subset_of_nonneg (range_mono hr.le) (fun n _ _ => hf n)
  have hcoef : 0 ≤ ((N % q : ℕ) : ℝ) / q := by positivity
  have hcoef1 : ((N % q : ℕ) : ℝ) / q ≤ 1 := (div_le_one hqR).mpr hrR
  have hdecomp : (N : ℝ) = (N / q : ℕ) * (q : ℝ) + (N % q : ℕ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm : N = N / q * q + N % q)
  rw [real_periodic_sum_div_mod]
  have hid : (N / q : ℕ) * (∑ n ∈ range q, f n) + ∑ n ∈ range (N % q), f n -
      (N : ℝ) / q * ∑ n ∈ range q, f n =
      (∑ n ∈ range (N % q), f n) -
        ((N % q : ℕ) : ℝ) / q * ∑ n ∈ range q, f n := by
    rw [hdecomp]
    field_simp
    ring
  rw [hid, abs_le]
  constructor <;> nlinarith

/-- Two prefix errors give the interval error, uniformly in its location. -/
theorem nonnegative_periodic_interval_error {q : ℕ} (hq : 0 < q)
    (f : ZMod q → ℝ) (hf : ∀ a, 0 ≤ f a) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, f n) - ((b : ℝ) - a) / q * ∑ n ∈ range q, f n| ≤
      2 * ∑ n ∈ range q, f n := by
  have ha := nonnegative_periodic_prefix_error hq f hf a
  have hb := nonnegative_periodic_prefix_error hq f hf b
  rw [sum_Ico_eq_sub (fun n : ℕ => f (n : ZMod q)) hab]
  calc
    _ = |((∑ n ∈ range b, f n) - (b : ℝ) / q * ∑ n ∈ range q, f n) -
        ((∑ n ∈ range a, f n) - (a : ℝ) / q * ∑ n ∈ range q, f n)| := by
      congr 1
      ring
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveCRT
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Chinese remainder counts for the sieve -/

namespace JointDickman

open Finset

/-- Uniform residue sums factor over any finite pairwise coprime family. -/
theorem crt_period_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ) :
    (∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i))) =
      ∏ i, ∑ a : ZMod (m i), f i a := by
  classical
  let : NeZero (∏ i, m i) := ⟨prod_ne_zero_iff.mpr (fun i _ => (hm i).ne')⟩
  let e := ZMod.prodEquivPi m hcop
  have hsum : (∑ a : ZMod (∏ i, m i), ∏ i, f i (e a i)) =
      ∏ i, ∑ b : ZMod (m i), f i b := by
    rw [Fintype.sum_equiv e.toEquiv (fun a => ∏ i, f i (e a i))
      (fun b => ∏ i, f i (b i)) (fun _ => rfl)]
    exact (Fintype.prod_sum f).symm
  have hperiod : (∑ a : ZMod (∏ i, m i), ∏ i, f i (e a i)) =
      ∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i)) := by
    have h := residue_sum_eq_range (fun a : ZMod (∏ i, m i) =>
      ((∏ i, f i (e a i) : ℝ) : ℂ))
    have heval (n : ℕ) : e (n : ZMod (∏ i, m i)) = (n : ∀ i, ZMod (m i)) :=
      map_natCast e n
    simp only [heval, Pi.natCast_apply] at h
    exact_mod_cast h
  exact hperiod.symm.trans hsum

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRemainders
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary bounds for the total sieve remainder

A crude fixed power of the level suffices: the manuscript allows a fixed
sieve cutoff sufficiently small compared with the counting scale.
-/

namespace JointDickman

open Finset

/-- Fixed exponential weights in the number of prime factors admit a
fixed polynomial bound in the product. -/
theorem prime_card_power_le_product_power (D : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime) (k : ℕ) :
    k ^ D.card ≤ (∏ p ∈ D, p) ^ k := by
  calc
    _ = ∏ _p ∈ D, k := by simp
    _ ≤ ∏ p ∈ D, p ^ k := prod_le_prod' (fun p hp =>
      k.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (hD p hp).two_le k))
    _ = _ := prod_pow D k id

/-- Distinct subsets give distinct squarefree products; summing their
fixed-factor-count weights below `N` costs at most `N^(k+1)+N^k`. -/
theorem sieve_level_power_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k N : ℕ) :
    (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N), k ^ D.card) ≤
      (N + 1) * N ^ k := by
  classical
  let S := P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N)
  have hinj : Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (↑S : Set (Finset ℕ)) := by
    intro D hD E hE heq
    exact primeProduct_injective hP
      (mem_powerset.mp (mem_filter.mp hD).1)
      (mem_powerset.mp (mem_filter.mp hE).1) heq
  have hsub : S.image (fun D => ∏ p ∈ D, p) ⊆ range (N + 1) := by
    intro d hd
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hd
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2)
  calc
    _ ≤ ∑ D ∈ S, (∏ p ∈ D, p) ^ k := by
      apply sum_le_sum
      intro D hD
      exact prime_card_power_le_product_power D
        (fun p hp => hP p (mem_powerset.mp (mem_filter.mp hD).1 hp)) k
    _ = ∑ d ∈ S.image (fun D => ∏ p ∈ D, p), d ^ k := (sum_image (f := fun d : ℕ => d ^ k) hinj).symm
    _ ≤ ∑ d ∈ range (N + 1), d ^ k := sum_le_sum_of_subset hsub
    _ ≤ ∑ _d ∈ range (N + 1), N ^ k := by
      apply sum_le_sum
      intro d hd
      exact Nat.pow_le_pow_left (Nat.le_of_lt_succ (mem_range.mp hd)) k
    _ = _ := by simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_WeightedSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reducing local weights by random forbidding

The upper sieve is applied to deterministic forbidden congruences. Randomly
forbidding each form converts that bound to the product of its local weights,
without changing the remainder. The transfer below is exact on finite sets;
the deterministic upper-sieve estimate is a separate published input.
-/

namespace JointDickman

open Finset

private theorem avoidsSelected_eq_product {ι : Type*} [DecidableEq ι]
    (S E : Finset ι) : avoidsSelected S E = ∏ i ∈ S, if i ∈ E then (0 : ℝ) else 1 := by
  classical
  by_cases h : Disjoint S E
  · rw [avoidsSelected, ite_eq_left h]
    symm
    apply prod_eq_one
    intro i hi
    have hn : i ∉ E := fun he => Finset.disjoint_left.mp h hi he
    simp [hn]
  · rw [avoidsSelected, ite_eq_right h]
    symm
    obtain ⟨i, hi, he⟩ := Finset.not_disjoint_iff.mp h
    exact prod_eq_zero hi (by simp [he])

/-- Average survival is exactly the product of the retained local weights. -/
theorem bernoulliSubsetMass_avoids {ι : Type*} [DecidableEq ι]
    (P E : Finset ι) (hE : E ⊆ P) (θ : ι → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S * avoidsSelected S E) =
      ∏ i ∈ E, θ i := by
  simp_rw [avoidsSelected_eq_product]
  rw [bernoulliSubsetMass_tilt]
  calc
    (∏ i ∈ P, (1 - (1 - θ i) + (1 - θ i) * if i ∈ E then (0 : ℝ) else 1)) =
        ∏ i ∈ P, if i ∈ E then θ i else 1 := by
      apply prod_congr rfl
      intro i _
      split_ifs <;> ring
    _ = ∏ i ∈ E, θ i := by
      rw [← prod_subset hE]
      · apply prod_congr rfl
        intro i hi
        simp [hi]
      · intro i _ hi
        simp [hi]

/-- Exact finite expectation identity for a population of points. -/
theorem randomized_sifted_mass {ι X : Type*} [DecidableEq ι] [Fintype X]
    (P : Finset ι) (E : X → Finset ι) (hE : ∀ x, E x ⊆ P)
    (w : X → ℝ) (θ : ι → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
      ∑ x, w x * avoidsSelected S (E x)) = ∑ x, w x * ∏ i ∈ E x, θ i := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  calc
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        (w x * avoidsSelected S (E x))) =
      w x * ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        avoidsSelected S (E x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      ring
    _ = _ := by rw [bernoulliSubsetMass_avoids P (E x) (hE x)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_UpperSieveInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published finite-event upper sieve

Theorem 2.4 of Kevin Ford, *Sieve Methods Lecture Notes, Spring 2023*,
page 18, https://ford126.web.illinois.edu/sieve2023.pdf, in its general
probability-space formulation (Section 1.2). The sum of absolute remainders
is only over squarefree products at most the sifting bound. No arithmetic
progression estimate or application-specific weight bound is assumed here.
-/

namespace JointDickman

open Finset

/-- Deleting sieve primes also preserves the dimension condition. -/
theorem SieveDimension.subset {P S : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hd : SieveDimension P g κ A z) (hS : S ⊆ P)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    SieveDimension S g κ A z := by
  intro y v hy hyv hvz
  apply le_trans _ (hd y v hy hyv hvz)
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact mem_filter.mpr ⟨hS (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  · intro p hp
    exact inv_nonneg.mpr (by linarith [(hg p (hS (mem_filter.mp hp).1)).2])
  · intro p hp _
    exact (one_le_inv₀ (by linarith [(hg p (mem_filter.mp hp).1).2])).mpr
      (by linarith [(hg p (mem_filter.mp hp).1).1])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveDimension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sieve dimension from Mertens' estimate -/

namespace JointDickman

open Finset

/-- The possible prime at the lower endpoint costs at most `1 / log y`. -/
theorem closed_prime_interval_sum_le
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : Finset ℕ) (y v : ℝ),
      (∀ p ∈ P, p.Prime) → 2 ≤ y → y ≤ v →
      (∑ p ∈ P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v),
        1 / (p : ℝ)) ≤ Real.log (Real.log v / Real.log y) + K / Real.log y := by
  obtain ⟨C, hC, hbound⟩ := prime_interval_mertens_error hM
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro P y v hP hy hyv
  have hy0 : 0 ≤ y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlv : 0 < Real.log v := Real.log_pos (by linarith)
  have hlogle : Real.log y ≤ Real.log v := Real.log_le_log (by linarith) hyv
  have hnle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hln : Real.log y ≤ (⌊y⌋₊ : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < y by linarith), Nat.lt_floor_add_one y]
  have hnpos : (0 : ℝ) < ⌊y⌋₊ := hly.trans_le hln
  have hnot : ⌊y⌋₊ ∉ largePrimeSet v y := by
    intro hn
    exact (not_lt_of_ge hnle) (mem_filter.mp hn).2
  have hsub : P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v) ⊆
      insert ⌊y⌋₊ (largePrimeSet v y) := by
    intro p hp
    obtain ⟨hpP, hpy, hpv⟩ := mem_filter.mp hp
    by_cases hlt : y < (p : ℝ)
    · apply mem_insert_of_mem
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpv, hP p hpP⟩, hlt⟩
    · have heq : (p : ℝ) = y := le_antisymm (le_of_not_gt hlt) hpy
      apply mem_insert.mpr
      left
      rw [← heq, Nat.floor_natCast]
  calc
    _ ≤ ∑ p ∈ insert ⌊y⌋₊ (largePrimeSet v y), 1 / (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 1 / (⌊y⌋₊ : ℝ) + ∑ p ∈ largePrimeSet v y, 1 / (p : ℝ) := sum_insert hnot
    _ ≤ 1 / Real.log y +
        ((Real.log (Real.log v) - Real.log (Real.log y)) +
          (C / Real.log v + C / Real.log y)) := by
      apply add_le_add
      · exact one_div_le_one_div_of_le hly hln
      · linarith [(abs_le.mp (hbound y v hy hyv)).2]
    _ ≤ Real.log (Real.log v / Real.log y) + (2 * C + 1) / Real.log y := by
      rw [Real.log_div hlv.ne' hly.ne']
      have hd := div_le_div_of_nonneg_left hC hly hlogle
      simp only [add_div, mul_div_assoc]
      linarith

/-- A fixed number of forbidden classes per prime has bounded dimension.
The dimension `2*k` is deliberately sufficient, rather than optimal. -/
theorem sieveDimension_of_reciprocal_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℝ} (hk : 0 < k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : Finset ℕ) (g : ℕ → ℝ) (z : ℝ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ)) →
      SieveDimension P g (2 * k) A z := by
  obtain ⟨K, hK, hbound⟩ := closed_prime_interval_sum_le hM
  refine ⟨2 * k * K, by positivity, ?_⟩
  intro P g z hP hg y v hy hyv _
  let S := P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v)
  have hsub : S ⊆ P := filter_subset _ _
  have hsum : (∑ p ∈ S, g p) ≤ k * ∑ p ∈ S, 1 / (p : ℝ) := by
    rw [mul_sum]
    exact sum_le_sum (fun p hp => by simpa only [mul_one_div] using (hg p (hsub hp)).2.2)
  calc
    _ ≤ Real.exp (2 * ∑ p ∈ S, g p) :=
      inverse_product_le_exp S g (fun p hp => ⟨(hg p (hsub hp)).1, (hg p (hsub hp)).2.1⟩)
    _ ≤ Real.exp (2 * k *
        (Real.log (Real.log v / Real.log y) + K / Real.log y)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (hbound P y v hP hy hyv) hk.le]
    _ = (Real.log v / Real.log y) ^ (2 * k) *
        Real.exp ((2 * k * K) / Real.log y) := by
      have hp : 0 < Real.log v / Real.log y :=
        div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
      rw [Real.rpow_def_of_pos hp, ← Real.exp_add]
      congr 1
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_WeightedUpperSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing weights in the published upper sieve

Independent random forbidding derives the Euler factors for arbitrary
retained weights in `[0,1]`. The original remainder is unchanged, and the
constant stays uniform over all the retained weights.
-/

namespace JointDickman

open Finset

theorem ford_weighted_upper_sieve (hFord : PublishedInputs.FordUpperSieveInput)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [Fintype X]
      (P : Finset ℕ) (E : X → Finset ℕ) (w : X → ℝ) (M z : ℝ)
      (g θ : ℕ → ℝ), 2 ≤ z → 0 ≤ M → (∀ x, 0 ≤ w x) →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) → (∀ x, E x ⊆ P) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) → SieveDimension P g κ A z →
      (∑ x, w x * ∏ p ∈ E x, θ p) ≤
        C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) +
          ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
            |sieveRemainder E w M g D| := by
  classical
  obtain ⟨C, hC, hbound⟩ := hFord κ A hκ hA
  refine ⟨C, hC, ?_⟩
  intro X _ P E w M z g θ hz hM hw hP hE hg hθ hd
  let R := ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
    |sieveRemainder E w M g D|
  have hq : ∀ p ∈ P, 0 ≤ 1 - θ p ∧ 1 - θ p ≤ 1 := by
    intro p hp
    constructor <;> linarith [(hθ p hp).1, (hθ p hp).2]
  have hupper (S : Finset ℕ) (hS : S ⊆ P) :
      (∑ x, w x * avoidsSelected S (E x)) ≤
        C * M * (∏ p ∈ S, (1 - g p)) + R := by
    apply (hbound X S E w M z g hz hM hw (fun p hp => hP p (hS hp))
      (fun p hp => hg p (hS hp)) (hd.subset hS hg)).trans
    apply add_le_add le_rfl
    apply sum_le_sum_of_subset_of_nonneg
    · intro D hD
      obtain ⟨hDS, hDz⟩ := mem_filter.mp hD
      exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp hDS).trans hS), hDz⟩
    · intro D _ _
      exact abs_nonneg _
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S *
        ∑ x, w x * avoidsSelected S (E x) :=
      (randomized_sifted_mass P E hE w θ).symm
    _ ≤ ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S *
        (C * M * (∏ p ∈ S, (1 - g p)) + R) := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left (hupper S (mem_powerset.mp hS))
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq)
    _ = C * M * (∑ S ∈ P.powerset,
          bernoulliSubsetMass P (fun p => 1 - θ p) S * ∏ p ∈ S, (1 - g p)) +
        R * (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S) := by
      simp_rw [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro S _ <;> ring
    _ = C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) + R := by
      rw [bernoulliSubsetMass_tilt, bernoulliSubsetMass_sum, mul_one]
      congr 2
      apply prod_congr rfl
      intro p _
      ring

/-- The ready-to-apply bound: only Ford and Mertens remain published inputs;
no abstract sieve dimension hypothesis remains. -/
theorem weighted_upper_sieve_from_published
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [Fintype X]
      (P : Finset ℕ) (E : X → Finset ℕ) (w : X → ℝ) (M z : ℝ)
      (g θ : ℕ → ℝ), 2 ≤ z → 0 ≤ M → (∀ x, 0 ≤ w x) →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) → (∀ x, E x ⊆ P) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ)) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ x, w x * ∏ p ∈ E x, θ p) ≤
        C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) +
          ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
            |sieveRemainder E w M g D| := by
  obtain ⟨A, hA, hdim⟩ := sieveDimension_of_reciprocal_bound hM hk
  obtain ⟨C, hC, hbound⟩ := ford_weighted_upper_sieve hFord
    (show 0 < 2 * k by positivity) hA
  refine ⟨C, hC, ?_⟩
  intro X _ P E w M z g θ hz hM hw hP hE hg hθ
  exact hbound X P E w M z g θ hz hM hw hP hE
    (fun p hp => ⟨(hg p hp).1, by linarith [(hg p hp).2.1]⟩) hθ
    (hdim P g z (fun p hp => (hP p hp).1) hg)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RootSelection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent selection of form roots, including repeated roots -/

namespace JointDickman

open Finset

/-- Uniform survival mass for a deterministic root set. -/
theorem root_survival_mean {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) (T : Finset α) :
    (∑ x : α, (if x ∈ T then (0 : ℝ) else 1)) / Fintype.card α =
      1 - (T.card : ℝ) / Fintype.card α := by
  have hx (x : α) : (if x ∈ T then (0 : ℝ) else 1) =
      1 - (if x ∈ T then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  simp_rw [hx]
  rw [sum_sub_distrib]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one,
    sum_ite_mem, sum_const]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
  simp [sub_div, hcard]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_UnionSelection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent selection of finite forbidden sets -/

namespace JointDickman

open Finset

/-- Independent form choices work equally for finite sets of zeros, such
as lines in a residue plane. Intersections between the sets cause no loss. -/
theorem bernoulli_union_survival {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) (θ : ι → ℝ) (x : α) :
    (∑ S ∈ I.powerset, bernoulliSubsetMass I (fun i => 1 - θ i) S *
      (if x ∈ S.biUnion F then 0 else 1)) =
      ∏ i ∈ I.filter (fun i => x ∈ F i), θ i := by
  classical
  let E := I.filter (fun i => x ∈ F i)
  have hid (S : Finset ι) (hS : S ⊆ I) :
      avoidsSelected S E = if x ∈ S.biUnion F then 0 else 1 := by
    have hiff : Disjoint S E ↔ x ∉ S.biUnion F := by
      constructor
      · intro h hx
        obtain ⟨i, hiS, hi⟩ := mem_biUnion.mp hx
        exact disjoint_left.mp h hiS (mem_filter.mpr ⟨hS hiS, hi⟩)
      · intro h
        apply disjoint_left.mpr
        intro i hiS hiE
        exact h (mem_biUnion.mpr ⟨i, hiS, (mem_filter.mp hiE).2⟩)
    unfold avoidsSelected
    by_cases hx : x ∈ S.biUnion F
    · have hn : ¬ Disjoint S E := fun h => (hiff.mp h) hx
      simp [hn, hx]
    · simp [hiff.mpr hx, hx]
  have h := bernoulliSubsetMass_avoids I E (filter_subset _ _) θ
  apply Eq.trans _ h
  apply sum_congr rfl
  intro S hS
  rw [hid S (mem_powerset.mp hS)]

/-- The mean density of the surviving residue set is the exact residue
average of all retained form weights. -/
theorem bernoulli_union_density {ι α : Type*} [DecidableEq ι]
    [Fintype α] [DecidableEq α] (hα : 0 < Fintype.card α)
    (I : Finset ι) (F : ι → Finset α) (θ : ι → ℝ) :
    (∑ S ∈ I.powerset, bernoulliSubsetMass I (fun i => 1 - θ i) S *
      (1 - ((S.biUnion F).card : ℝ) / Fintype.card α)) =
      (∑ x : α, ∏ i ∈ I.filter (fun i => x ∈ F i), θ i) / Fintype.card α := by
  simp_rw [← root_survival_mean hα, ← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  exact bernoulli_union_survival I F θ x

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RandomRootSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independently randomized root sets

Averaging the uniform deterministic bound preserves its remainder and
factors its main term. The root sets at a prime may contain coincident
roots of several forms; only their union and its cardinality matter.
-/

namespace JointDickman

open Finset

/-- Exact expectation of a product under the finite product law. -/
theorem finiteProductMass_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ F : ∀ i, Ω i → ℝ) :
    (∑ ω, finiteProductMass μ ω * ∏ i, F i (ω i)) =
      ∏ i, ∑ x, μ i x * F i x := by
  simp_rw [finiteProductMass, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => μ i x * F i x)).symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicRectangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse errors for a periodic nonnegative weight in a rectangle -/

namespace JointDickman

open Finset

/-- The rectangle error retains the mass in a single residue square,
which is essential when only a few residue lines are allowed. -/
theorem nonnegative_periodic_rectangle_error {q : ℕ} (hq : 0 < q)
    (F : ZMod q → ZMod q → ℝ) (hF : ∀ r s, 0 ≤ F r s)
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        (((b : ℝ) - a) * ((d : ℝ) - c) / (q : ℝ) ^ 2) *
          ∑ r ∈ range q, ∑ s ∈ range q, F r s| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / q + 2) *
        ∑ r ∈ range q, ∑ s ∈ range q, F r s := by
  let G := fun r : ZMod q => ∑ s ∈ range q, F r s
  let M := ∑ r ∈ range q, G r
  let L₁ : ℝ := (b : ℝ) - a
  let L₂ : ℝ := (d : ℝ) - c
  have hL₁ : 0 ≤ L₁ := sub_nonneg.mpr (by exact_mod_cast hab)
  have hL₂ : 0 ≤ L₂ := sub_nonneg.mpr (by exact_mod_cast hcd)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hG (r : ZMod q) : 0 ≤ G r := sum_nonneg (fun s _ => hF r s)
  have hmass : 0 ≤ M := sum_nonneg (fun r _ => hG r)
  have hrow (m : ℕ) := nonnegative_periodic_interval_error hq (F m) (hF m) hcd
  have houter := nonnegative_periodic_interval_error hq G hG hab
  change |(∑ m ∈ Ico a b, G m) - L₁ / q * M| ≤ 2 * M at houter
  have hsumG : (∑ m ∈ Ico a b, G m) ≤ (L₁ / q + 2) * M := by
    linarith [(abs_le.mp houter).2]
  have hsumrow : |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
      L₂ / q * ∑ m ∈ Ico a b, G m| ≤ 2 * ∑ m ∈ Ico a b, G m := by
    rw [mul_sum, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ m ∈ Ico a b, 2 * G m := by
        apply sum_le_sum
        intro m _
        exact hrow m
      _ = _ := (mul_sum _ _ _).symm
  have hscaled : |L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| ≤
      L₂ / q * (2 * M) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hL₂ hq0.le)]
    exact mul_le_mul_of_nonneg_left houter (div_nonneg hL₂ hq0.le)
  change |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
    (L₁ * L₂ / (q : ℝ) ^ 2) * M| ≤ 2 * ((L₁ + L₂) / q + 2) * M
  calc
    _ = |((∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        L₂ / q * ∑ m ∈ Ico a b, G m) +
        L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        L₂ / q * ∑ m ∈ Ico a b, G m| +
        |L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| := abs_add_le _ _
    _ ≤ 2 * (∑ m ∈ Ico a b, G m) + L₂ / q * (2 * M) :=
      add_le_add hsumrow hscaled
    _ ≤ 2 * ((L₁ / q + 2) * M) + L₂ / q * (2 * M) := by linarith
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRectangleCRT
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chinese remainder counts in two variables -/

namespace JointDickman

open Finset

/-- Complete residue squares factor by two applications of the CRT. -/
theorem crt_rectangle_period_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (F : ∀ i, ZMod (m i) → ZMod (m i) → ℝ) :
    (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i),
      ∏ i, F i (r : ZMod (m i)) (s : ZMod (m i))) =
      ∏ i, ∑ r : ZMod (m i), ∑ s : ZMod (m i), F i r s := by
  calc
    _ = ∑ r ∈ range (∏ i, m i), ∏ i, ∑ s : ZMod (m i), F i (r : ZMod (m i)) s := by
      apply sum_congr rfl
      intro r _
      exact crt_period_sum m hm hcop (fun i s => F i (r : ZMod (m i)) s)
    _ = _ := crt_period_sum m hm hcop (fun i r => ∑ s : ZMod (m i), F i r s)

/-- A family of prescribed residue-pair sets has exactly the product of
its local cardinalities in a complete square. -/
theorem crt_pair_period_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i) × ZMod (m i))) :
    (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i),
      if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) =
      ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hind (r s : ℕ) :
      (∏ i, if ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) =
        if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then 1 else 0 := by
    split_ifs with h
    · exact prod_eq_one (fun i _ => ite_eq_left (h i))
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [← hind]
  rw [crt_rectangle_period_sum m hm hcop (fun i r s => if (r, s) ∈ A i then (1 : ℝ) else 0)]
  apply prod_congr rfl
  intro i _
  rw [← Fintype.sum_prod_type (fun rs : ZMod (m i) × ZMod (m i) =>
    if rs ∈ A i then (1 : ℝ) else 0)]
  simp

/-- The two-dimensional CRT remainder retains the exact number of
prescribed residue pairs. -/
theorem crt_pair_rectangle_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i) × ZMod (m i)))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) -
      (((b : ℝ) - a) * ((d : ℝ) - c) / (∏ i, (m i : ℝ)) ^ 2) *
        ∏ i, ((A i).card : ℝ)| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ i, (m i : ℝ)) + 2) *
        ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hM : 0 < ∏ i, m i := prod_pos (fun i _ => hm i)
  let : NeZero (∏ i, m i) := ⟨hM.ne'⟩
  let e := ZMod.prodEquivPi m hcop
  let F := fun r s : ZMod (∏ i, m i) => if ∀ i, (e r i, e s i) ∈ A i then (1 : ℝ) else 0
  have hF (r s : ℕ) : F r s =
      if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then 1 else 0 := by
    have hr : e (r : ZMod (∏ i, m i)) = (r : ∀ i, ZMod (m i)) := map_natCast e r
    have hs : e (s : ZMod (∏ i, m i)) = (s : ∀ i, ZMod (m i)) := map_natCast e s
    simp [F, hr, hs]
  have hmass : (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i), F r s) =
      ∏ i, ((A i).card : ℝ) := by
    simp_rw [hF]
    exact crt_pair_period_count m hm hcop A
  have h := nonnegative_periodic_rectangle_error hM F
    (fun r s => by dsimp [F]; split_ifs <;> norm_num) hab hcd
  rw [hmass] at h
  simpa only [hF, Nat.cast_prod] using h

/-- Prime-set specialization with the local densities already factored. -/
theorem prime_pair_rectangle_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ p ∈ P, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ((d : ℝ) - c) *
        ∏ p ∈ P, ((A p).card : ℝ) / (p : ℝ) ^ 2| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ P, (p : ℝ)) + 2) *
        ∏ p ∈ P, ((A p).card : ℝ) := by
  have hcop : Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have h := crt_pair_rectangle_error (fun p : P => (p : ℕ))
    (fun p => (hP p p.property).pos) hcop (fun p => A p) hab hcd
  simp only [P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ)),
    P.prod_coe_sort (fun p : ℕ => (p : ℝ)), Subtype.forall] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  rw [prod_div_distrib, ← prod_pow]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRectangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangle sieve with an explicit arithmetic remainder -/

namespace JointDickman

open Finset

/-- Actual intersections in a rectangle have the CRT error. -/
theorem pair_root_sieve_remainder (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder
      (fun n : (Ico a b) × (Ico c d) => pairRootEvents P A n.1 n.2)
      (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c))
      (fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2) D| ≤
        2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ D, (p : ℝ)) + 2) *
          ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  have hcond (r s : ℕ) : D ⊆ pairRootEvents P A r s ↔
      ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p := by
    constructor
    · intro h p hp
      exact (mem_filter.mp (h hp)).2
    · intro h p hp
      exact mem_filter.mpr ⟨hD hp, h p hp⟩
  unfold sieveRemainder sieveIntersection
  simp_rw [hcond]
  rw [Fintype.sum_prod_type]
  have hout : (∑ r : Ico a b, ∑ s : Ico c d,
      if ∀ p ∈ D, ((r.val : ZMod p), (s.val : ZMod p)) ∈ A p then (1 : ℝ) else 0) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0 := by
    apply Eq.trans _ ((Ico a b).sum_coe_sort (fun r : ℕ =>
      ∑ s ∈ Ico c d, if ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0))
    apply sum_congr rfl
    intro r _
    exact (Ico c d).sum_coe_sort (fun s : ℕ =>
      if ∀ p ∈ D, ((r.val : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0)
  rw [hout]
  exact prime_pair_rectangle_error D (fun p hp => hP p (hD hp)) A hab hcd

/-- With at most `k*p` local residue pairs, the denominator in the CRT
error cancels. This includes unions of at most `k` affine lines. -/
theorem pair_root_sieve_remainder_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (k : ℕ)
    (hA : ∀ p ∈ P, (A p).card ≤ k * p)
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder
      (fun n : (Ico a b) × (Ico c d) => pairRootEvents P A n.1 n.2)
      (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c))
      (fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2) D| ≤
        2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * ∏ p ∈ D, (p : ℝ)) *
          (k : ℝ) ^ D.card := by
  have hprod : 0 < ∏ p ∈ D, (p : ℝ) := prod_pos (fun p hp => by
    exact_mod_cast (hP p (hD hp)).pos)
  have hL : 0 ≤ ((b : ℝ) - a) + ((d : ℝ) - c) := add_nonneg
    (sub_nonneg.mpr (by exact_mod_cast hab)) (sub_nonneg.mpr (by exact_mod_cast hcd))
  have hcount : (∏ p ∈ D, ((A p).card : ℝ)) ≤
      (k : ℝ) ^ D.card * ∏ p ∈ D, (p : ℝ) := by
    calc
      _ ≤ ∏ p ∈ D, (k : ℝ) * p := Finset.prod_le_prod (by intros; positivity)
        (fun p hp => by exact_mod_cast hA p (hD hp))
      _ = _ := by rw [prod_mul_distrib]; simp
  apply (pair_root_sieve_remainder P hP A hab hcd hD).trans
  calc
    _ ≤ 2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ D, (p : ℝ)) + 2) *
        ((k : ℝ) ^ D.card * ∏ p ∈ D, (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by field_simp

private theorem sum_rectangle_subtype (a b c d : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ x : (Ico a b) × (Ico c d), F x.1 x.2) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d, F r s := by
  rw [Fintype.sum_prod_type]
  have hin (r : Ico a b) : (∑ s : Ico c d, F r s) = ∑ s ∈ Ico c d, F r s :=
    (Ico c d).sum_coe_sort (fun s => F r s)
  simp_rw [hin]
  exact (Ico a b).sum_coe_sort (fun r => ∑ s ∈ Ico c d, F r s)

/-- The weighted rectangle sieve, with all intersection errors evaluated.
The only analytic assumptions are the cited Ford and Mertens inputs. -/
theorem weighted_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (A : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (θ : ℕ → ℝ)
      (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, (A p).card ≤ k * p) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p ∈ pairRootEvents P A r s, θ p) ≤
        C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / (p : ℝ) ^ 2 +
            ((A p).card : ℝ) / (p : ℝ) ^ 2 * θ p)) +
        2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_upper_sieve_from_published hFord hM
    (show (0 : ℝ) < k by exact_mod_cast hk)
  refine ⟨C, hC, ?_⟩
  intro P A θ a b c d Z hab hcd hZ hP hA hθ
  let E := fun x : (Ico a b) × (Ico c d) => pairRootEvents P A x.1 x.2
  let g := fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2
  let L := ((b : ℝ) - a) + ((d : ℝ) - c)
  have hL : 0 ≤ L := add_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))
    (sub_nonneg.mpr (by exact_mod_cast hcd))
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ (k : ℝ) / p := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    have hcard : ((A p).card : ℝ) ≤ (k : ℝ) * p := by exact_mod_cast hA p hp
    have hkp : 2 * (k : ℝ) ≤ p := by exact_mod_cast (hP p hp).2.2
    have hsmall : g p ≤ (k : ℝ) / p := by
      calc
        _ ≤ ((k : ℝ) * p) / (p : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hcard (sq_nonneg _)
        _ = _ := by field_simp
    refine ⟨by dsimp [g] <;> positivity, ?_, hsmall⟩
    exact hsmall.trans ((div_le_iff₀ hp0).mpr (by linarith))
  have h := hbound ((Ico a b) × (Ico c d)) P E (fun _ => 1)
    (((b : ℝ) - a) * ((d : ℝ) - c)) Z g θ (by exact_mod_cast hZ)
    (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))
      (sub_nonneg.mpr (by exact_mod_cast hcd))) (by intros; norm_num)
    (fun p hp => ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2.1⟩)
    (fun x => filter_subset _ _) hg hθ
  simp only [one_mul] at h
  have hleft : (∑ x : (Ico a b) × (Ico c d), ∏ p ∈ E x, θ p) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p ∈ pairRootEvents P A r s, θ p :=
    sum_rectangle_subtype a b c d (fun r s => ∏ p ∈ pairRootEvents P A r s, θ p)
  rw [hleft] at h
  have heq : P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ (Z : ℝ)) =
      P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z) := by
    ext D
    simp only [mem_filter, Nat.cast_le]
  rw [heq] at h
  have hrem : (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
      |sieveRemainder E (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c)) g D|) ≤
      2 * (L + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
    calc
      _ ≤ ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
          2 * (L + 2 * Z) * (k : ℝ) ^ D.card := by
        apply sum_le_sum
        intro D hD
        have hDP := mem_powerset.mp (mem_filter.mp hD).1
        have hdZ : (∏ p ∈ D, (p : ℝ)) ≤ Z := by
          rw [← Nat.cast_prod]
          exact_mod_cast (mem_filter.mp hD).2
        apply (pair_root_sieve_remainder_le P (fun p hp => (hP p hp).1) A k hA hab hcd hDP).trans
        dsimp only [L]
        nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) D.card]
      _ = 2 * (L + 2 * Z) * ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
          (k : ℝ) ^ D.card := (mul_sum _ _ _).symm
      _ ≤ 2 * (L + 2 * Z) * ((Z + 1 : ℝ) * (Z : ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast sieve_level_power_sum P (fun p hp => (hP p hp).1) k Z
      _ = _ := by ring
  apply h.trans
  dsimp only [g, L] at hrem ⊢
  simpa only [mul_assoc] using add_le_add le_rfl hrem

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RandomRectangleSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent random forbidden sets in residue planes -/

namespace JointDickman

open Finset

theorem randomized_pair_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (Ω : P → Type) [∀ p, Fintype (Ω p)]
      (μ : ∀ p, Ω p → ℝ) (A : ∀ p : P, Ω p → Finset (ZMod p.val × ZMod p.val))
      (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p x, 0 ≤ μ p x) → (∀ p, ∑ x, μ p x = 1) →
      (∀ p x, (A p x).card ≤ k * p.val) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P, ∑ x, μ p x *
        (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p x then 0 else 1)) ≤
      C * ((b : ℝ) - a) * ((d : ℝ) - c) * (∏ p : P, ∑ x, μ p x *
        (1 - ((A p x).card : ℝ) / (p.val : ℝ) ^ 2)) +
      2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P Ω _ μ A a b c d Z hab hcd hZ hP hμ hμ1 hA
  let R := 2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k
  let roots (ω : ∀ p, Ω p) (q : ℕ) : Finset (ZMod q × ZMod q) :=
    if hq : q ∈ P then A ⟨q, hq⟩ (ω ⟨q, hq⟩) else ∅
  have hroot (ω : ∀ p, Ω p) (p : P) : roots ω p.val = A p (ω p) := by
    simp [roots, p.property]
  have hprod (ω : ∀ p, Ω p) (r s : ℕ) :
      (∏ p ∈ pairRootEvents P (roots ω) r s, (0 : ℝ)) =
        ∏ p : P, if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then 0 else 1 := by
    calc
      _ = ∏ p ∈ P, if ((r : ZMod p), (s : ZMod p)) ∈ roots ω p then (0 : ℝ) else 1 := by
        simp only [pairRootEvents, prod_filter]
      _ = ∏ p : P, if ((r : ZMod p.val), (s : ZMod p.val)) ∈ roots ω p.val then (0 : ℝ) else 1 :=
        (P.prod_coe_sort (fun p : ℕ =>
          if ((r : ZMod p), (s : ZMod p)) ∈ roots ω p then (0 : ℝ) else 1)).symm
      _ = _ := by simp_rw [hroot]
  have hpoint (ω : ∀ p, Ω p) :
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
        if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then (0 : ℝ) else 1) ≤
        C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2)) + R := by
    have h := hbound P (roots ω) (fun _ => 0) a b c d Z hab hcd hZ hP
      (fun p hp => by simpa [roots, hp] using hA ⟨p, hp⟩ (ω ⟨p, hp⟩))
      (by intros; norm_num)
    simp_rw [hprod] at h
    simpa only [mul_zero, add_zero,
      ← P.prod_coe_sort (fun p : ℕ => 1 - ((roots ω p).card : ℝ) / (p : ℝ) ^ 2), hroot] using h
  calc
    _ = ∑ ω, finiteProductMass μ ω *
        (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
          if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then (0 : ℝ) else 1) := by
      symm
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      exact (finiteProductMass_product_expectation μ
        (fun p x => if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p x then 0 else 1))
    _ ≤ ∑ ω, finiteProductMass μ ω *
        (C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2)) + R) := by
      apply sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hpoint ω) (finiteProductMass_nonneg μ hμ ω)
    _ = _ := by
      simp_rw [mul_add, sum_add_distrib]
      have hfirst : (∑ ω, finiteProductMass μ ω *
          (C * ((b : ℝ) - a) * ((d : ℝ) - c) *
            ∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2))) =
          C * ((b : ℝ) - a) * ((d : ℝ) - c) * ∏ p : P, ∑ x, μ p x *
            (1 - ((A p x).card : ℝ) / (p.val : ℝ) ^ 2) := by
        rw [← finiteProductMass_product_expectation, mul_sum]
        apply sum_congr rfl
        intro ω _
        ring
      rw [hfirst, ← sum_mul, finiteProductMass_sum μ hμ1, one_mul]
      dsimp [R]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveAffineLines
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinality of a proper affine line over a prime residue field -/

namespace JointDickman

open Finset

/-- A proper affine line has at most `p` residue pairs. -/
theorem affineResidueLine_card_le {p : ℕ} (hp : p.Prime)
    (a b c : ZMod p) (hproper : a ≠ 0 ∨ b ≠ 0) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (affineResidueLine a b c).card ≤ p := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  change (affineResidueLine a b c).card ≤ p
  rcases hproper with ha | hb
  · have hinj : Set.InjOn Prod.snd (↑(affineResidueLine a b c) : Set (ZMod p × ZMod p)) := by
      intro x hx y hy hxy
      apply Prod.ext _ hxy
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      rw [hxy] at hx'
      have heq : a * x.1 = a * y.1 := by linear_combination hx' - hy'
      exact mul_left_cancel₀ ha heq
    calc
      _ = ((affineResidueLine a b c).image Prod.snd).card := (card_image_iff.mpr hinj).symm
      _ ≤ (univ : Finset (ZMod p)).card := card_le_card (subset_univ _)
      _ = p := by simp
  · have hinj : Set.InjOn Prod.fst (↑(affineResidueLine a b c) : Set (ZMod p × ZMod p)) := by
      intro x hx y hy hxy
      apply Prod.ext hxy
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      rw [hxy] at hx'
      have heq : b * x.2 = b * y.2 := by linear_combination hx' - hy'
      exact mul_left_cancel₀ hb heq
    calc
      _ = ((affineResidueLine a b c).image Prod.fst).card := (card_image_iff.mpr hinj).symm
      _ ≤ (univ : Finset (ZMod p)).card := card_le_card (subset_univ _)
      _ = p := by simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FormRectangleSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independently weighted forms in a rectangle -/

namespace JointDickman

open Finset

/-- The rectangular form-weight bound with exact residue averages. Each
zero set may be any set of at most `p` pairs, in particular a proper line. -/
theorem form_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (F : ∀ p : P, Fin k → Finset (ZMod p.val × ZMod p.val))
      (θ : P → Fin k → ℝ) (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p i, (F p i).card ≤ p.val) → (∀ p i, 0 ≤ θ p i ∧ θ p i ≤ 1) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
        formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) ≤
      C * ((b : ℝ) - a) * ((d : ℝ) - c) *
        (∏ p : P, (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) / (p.val : ℝ) ^ 2) +
      2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := randomized_pair_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P F θ a b c d Z hab hcd hZ hP hF hθ
  let I : Finset (Fin k) := univ
  let Ω := {S : Finset (Fin k) // S ∈ I.powerset}
  let μ (p : P) (S : Ω) := bernoulliSubsetMass I (fun i => 1 - θ p i) S.val
  let A (p : P) (S : Ω) := S.val.biUnion (F p)
  have hμ (p : P) (S : Ω) : 0 ≤ μ p S :=
    bernoulliSubsetMass_nonneg (mem_powerset.mp S.property) (by
      intro i _
      constructor <;> linarith [(hθ p i).1, (hθ p i).2])
  have hμ1 (p : P) : ∑ S : Ω, μ p S = 1 := by
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S)]
    exact bernoulliSubsetMass_sum I _
  have hA (p : P) (S : Ω) : (A p S).card ≤ k * p.val := by
    calc
      _ ≤ ∑ i ∈ S.val, (F p i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ S.val, p.val := sum_le_sum (fun i _ => hF p i)
      _ = S.val.card * p.val := by simp
      _ ≤ I.card * p.val := Nat.mul_le_mul_right _ (card_le_card (mem_powerset.mp S.property))
      _ = _ := by simp [I]
  have hpoint (p : P) (r s : ℕ) :
      (∑ S : Ω, μ p S * (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p S then 0 else 1)) =
        formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val)) := by
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ S.val.biUnion (F p) then 0 else 1)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ S.biUnion (F p) then 0 else 1))]
    exact bernoulli_union_survival I (F p) (θ p) _
  have hdensity (p : P) :
      (∑ S : Ω, μ p S * (1 - ((A p S).card : ℝ) / (p.val : ℝ) ^ 2)) =
        (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) / (p.val : ℝ) ^ 2 := by
    let : NeZero p.val := ⟨(hP p.val p.property).1.ne_zero⟩
    have h := bernoulli_union_density
      (show 0 < Fintype.card (ZMod p.val × ZMod p.val) by
        simp only [Fintype.card_prod, ZMod.card]
        exact Nat.mul_pos (hP p.val p.property).1.pos (hP p.val p.property).1.pos) I (F p) (θ p)
    simp only [Fintype.card_prod, ZMod.card, ← pow_two, Nat.cast_pow] at h
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (1 - ((S.val.biUnion (F p)).card : ℝ) / (p.val : ℝ) ^ 2)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (1 - ((S.biUnion (F p)).card : ℝ) / (p.val : ℝ) ^ 2)), h]
    congr 1
    have hres (f : ZMod p.val → ℝ) : (∑ x, f x) = ∑ n ∈ range p.val, f n := by
      exact_mod_cast residue_sum_eq_range (fun x => (f x : ℂ))
    rw [Fintype.sum_prod_type]
    simp_rw [hres]
    rfl
  have h := hbound P (fun _ => Ω) μ A a b c d Z hab hcd hZ hP hμ hμ1 hA
  simpa only [hpoint, hdensity] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AffineRectangleSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted affine-line rectangle sieve -/

namespace JointDickman

open Finset

/-- The manuscript's rectangle sieve for proper affine forms, with the
exact local mean and an explicit polynomial remainder. -/
theorem affine_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (a b c : ∀ p : P, Fin k → ZMod p.val) (θ : P → Fin k → ℝ)
      (u v w x Z : ℕ), u ≤ v → w ≤ x → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p i, a p i ≠ 0 ∨ b p i ≠ 0) →
      (∀ p i, 0 ≤ θ p i ∧ θ p i ≤ 1) →
      (∑ r ∈ Ico u v, ∑ s ∈ Ico w x, ∏ p : P,
        affineFormWeight (a p) (b p) (c p) (θ p) (r : ZMod p.val) (s : ZMod p.val)) ≤
      C * ((v : ℝ) - u) * ((x : ℝ) - w) *
        (∏ p : P, (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          affineFormWeight (a p) (b p) (c p) (θ p)
            (r : ZMod p.val) (s : ZMod p.val)) / (p.val : ℝ) ^ 2) +
      2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  obtain ⟨C, hC, hbound⟩ := form_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P a b c θ u v w x Z huv hwx hZ hP hproper hθ
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).1.ne_zero⟩
  let F := fun (p : P) (i : Fin k) => affineResidueLine (a p i) (b p i) (c p i)
  have hF (p : P) (i : Fin k) : (F p i).card ≤ p.val :=
    affineResidueLine_card_le (hP p.val p.property).1 _ _ _ (hproper p i)
  have heq (p : P) (r s : ZMod p.val) :
      formSetWeight (F p) (θ p) (r, s) = affineFormWeight (a p) (b p) (c p) (θ p) r s := by
    simp [formSetWeight, F, affineResidueLine, prod_filter, affineFormWeight]
  simpa only [heq] using hbound P F θ u v w x Z huv hwx hZ hP hF hθ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AffineLocalFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact local means for the three forms b, c, b+jc -/

namespace JointDickman

open Finset

open Classical in
theorem sum_residueWeight {α : Type*} [Fintype α] (t : ℝ) (a : α) :
    ∑ x : α, residueWeight t a x = (Fintype.card α : ℝ) - 1 + t := by
  have heq (x : α) : residueWeight t a x = 1 + (if x = a then t - 1 else 0) := by
    by_cases h : x = a <;> simp [residueWeight, h]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true, if_true]
  ring

open Classical in
theorem sum_two_residueWeights {α : Type*} [Fintype α] (t u : ℝ) (a b : α)
    (hab : a ≠ b) :
    ∑ x : α, residueWeight t a x * residueWeight u b x =
      (Fintype.card α : ℝ) - 2 + t + u := by
  have heq (x : α) : residueWeight t a x * residueWeight u b x =
      1 + (if x = a then t - 1 else 0) + (if x = b then u - 1 else 0) := by
    by_cases ha : x = a <;> by_cases hb : x = b
    · exact False.elim (hab (ha.symm.trans hb))
    all_goals simp [residueWeight, ha, hb, hab, Ne.symm hab]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true, if_true]
  ring

open Classical in
theorem sum_squared_residueWeight {α : Type*} [Fintype α] (t : ℝ) (a : α) :
    ∑ x : α, residueWeight t a x ^ 2 = (Fintype.card α : ℝ) - 1 + t ^ 2 := by
  have heq (x : α) : residueWeight t a x ^ 2 = residueWeight (t ^ 2) a x := by
    by_cases h : x = a <;> simp [residueWeight, h]
  simp_rw [heq]
  exact sum_residueWeight _ _

open Classical in
theorem three_affine_residue_sum {p : ℕ} [Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) (t : ℝ) :
    (∑ b : ZMod p, ∑ c : ZMod p,
      residueWeight t 0 b * residueWeight t 0 c * residueWeight t 0 (b + j * c)) =
      t * ((p : ℝ) - 1 + t ^ 2) + ((p : ℝ) - 1) * ((p : ℝ) - 2 + 2 * t) := by
  rw [sum_comm]
  have hinner (c : ZMod p) : (∑ b : ZMod p,
      residueWeight t 0 b * residueWeight t 0 c * residueWeight t 0 (b + j * c)) =
      if c = 0 then t * ((p : ℝ) - 1 + t ^ 2) else (p : ℝ) - 2 + 2 * t := by
    by_cases hc : c = 0
    · subst c
      simp only [mul_zero, add_zero, residueWeight, ite_true, if_true]
      have hs := sum_squared_residueWeight t (0 : ZMod p)
      simp only [ZMod.card] at hs
      calc
        _ = t * ∑ b : ZMod p, residueWeight t 0 b ^ 2 := by
          rw [mul_sum]
          apply sum_congr rfl
          intro b _
          by_cases hb : b = 0
          · simp [residueWeight, hb]
            ring
          · simp [residueWeight, hb]
        _ = _ := by rw [hs]
    · have hroot : (0 : ZMod p) ≠ -(j * c) := by
        intro h
        have : j * c = 0 := neg_eq_zero.mp h.symm
        exact (mul_ne_zero hj hc) this
      have heq (b : ZMod p) : residueWeight t 0 (b + j * c) = residueWeight t (-(j * c)) b := by
        simp [residueWeight, add_eq_zero_iff_eq_neg]
      simp only [hc, residueWeight, ite_false, if_false, mul_one]
      change (∑ b : ZMod p, residueWeight t 0 b * residueWeight t 0 (b + j * c)) = _
      simp_rw [heq]
      simpa only [ZMod.card, two_mul, add_assoc] using
        sum_two_residueWeights t t (0 : ZMod p) (-(j * c)) hroot
  simp_rw [hinner]
  have heq (c : ZMod p) :
      (if c = 0 then t * ((p : ℝ) - 1 + t ^ 2) else (p : ℝ) - 2 + 2 * t) =
      ((p : ℝ) - 2 + 2 * t) +
        (if c = 0 then t * ((p : ℝ) - 1 + t ^ 2) - ((p : ℝ) - 2 + 2 * t) else 0) := by
    by_cases hc : c = 0 <;> simp [hc]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, sum_ite_eq', mem_univ,
    ite_true, if_true]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ThreeFormLocalBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local upper bounds for b, c, and b+jc

At primes not dividing j the exact three-form mean is bounded by the cube
of the single-form mean. Degenerate primes cost at most `1 + 24/p`.
-/

namespace JointDickman

open Finset

theorem residueWeight_nonneg {α : Type*} (a x : α) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ residueWeight t a x := by
  classical
  unfold residueWeight
  split_ifs <;> positivity

theorem residueWeight_le_one {α : Type*} (a x : α) {t : ℝ} (ht : t ≤ 1) :
    residueWeight t a x ≤ 1 := by
  classical
  unfold residueWeight
  split_ifs <;> linarith

theorem threeFormResidueMean_le_one {p : ℕ} [NeZero p] (j : ZMod p) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : threeFormResidueMean j t ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (div_le_one (sq_pos_of_pos hp0)).mpr
  calc
    _ ≤ ∑ _b : ZMod p, ∑ _c : ZMod p, (1 : ℝ) := by
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro c _
      calc
        _ ≤ 1 * 1 := mul_le_mul
          (by
            have h := mul_le_mul (residueWeight_le_one (0 : ZMod p) b ht1)
              (residueWeight_le_one (0 : ZMod p) c ht1)
              (residueWeight_nonneg (0 : ZMod p) c ht) zero_le_one
            simpa only [mul_one] using h)
          (residueWeight_le_one _ _ ht1) (residueWeight_nonneg _ _ ht) zero_le_one
        _ = 1 := mul_one _
    _ = _ := by simp [pow_two]

theorem threeFormResidueMean_nondegenerate {p : ℕ} [Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) {t : ℝ} (_ht : 0 ≤ t) (ht1 : t ≤ 1) :
    threeFormResidueMean j t ≤ (1 - (1 - t) / p) ^ 3 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hidentity : threeFormResidueMean j t = (1 - (1 - t) / p) ^ 3 -
      (1 - t) ^ 3 * ((p : ℝ) - 1) / (p : ℝ) ^ 3 := by
    unfold threeFormResidueMean
    rw [three_affine_residue_sum j hj]
    field_simp
    ring
  rw [hidentity]
  exact sub_le_self _ (by positivity)

theorem one_le_cube_singular_factor {x d : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    1 ≤ (1 - d * x) ^ 3 * (1 + 24 * x) := by
  have hdx : 0 ≤ d * x := mul_nonneg hd hx
  have hdxle : d * x ≤ x := mul_le_of_le_one_left hx hd1
  have hcube : (1 / 8 : ℝ) ≤ (1 - d * x) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show (1 / 2 : ℝ) ≤ 1 - d * x by linarith) 3
    norm_num at h
    exact h
  have hbernoulli : 1 - 3 * x ≤ (1 - d * x) ^ 3 := by
    have hprod := mul_nonneg (sq_nonneg (d * x)) (show 0 ≤ 3 - d * x by linarith)
    nlinarith
  have hextra := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 24 * x by positivity)
  nlinarith

theorem threeFormResidueMean_bound {p : ℕ} [Fact p.Prime]
    (j : ZMod p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    threeFormResidueMean j t ≤ (1 - (1 - t) / p) ^ 3 *
      (if j = 0 then 1 + 24 / (p : ℝ) else 1) := by
  by_cases hj : j = 0
  · rw [ite_eq_left hj]
    refine (threeFormResidueMean_le_one j ht ht1).trans ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    have hx : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    simpa only [div_eq_mul_inv, one_mul] using one_le_cube_singular_factor
      (by positivity : (0 : ℝ) ≤ 1 / p) hx (by linarith : 0 ≤ 1 - t)
      (by linarith : 1 - t ≤ 1)
  · rw [ite_eq_right hj, mul_one]
    exact threeFormResidueMean_nondegenerate j hj ht ht1

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ThreeFormSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three-form rectangle sieve with its singular factor -/

namespace JointDickman

open Finset

theorem real_residue_sum_eq_range {p : ℕ} [NeZero p] (f : ZMod p → ℝ) :
    (∑ r : ZMod p, f r) = ∑ n ∈ range p, f n := by
  have h := residue_sum_eq_range (fun r => (f r : ℂ))
  exact_mod_cast h

theorem real_residue_double_sum_eq_range {p : ℕ} [NeZero p]
    (f : ZMod p → ZMod p → ℝ) :
    (∑ r : ZMod p, ∑ s : ZMod p, f r s) =
      ∑ m ∈ range p, ∑ n ∈ range p, f m n := by
  rw [real_residue_sum_eq_range]
  apply sum_congr rfl
  intro m _
  exact real_residue_sum_eq_range _

theorem threeFormLocalFactor_eq_mean {p : ℕ} [NeZero p] (j : ℕ) (t : ℝ) :
    threeFormLocalFactor p j t = threeFormResidueMean (j : ZMod p) t := by
  unfold threeFormLocalFactor threeFormResidueMean
  rw [real_residue_double_sum_eq_range]

theorem threeFormLocalFactor_nonneg (p j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ threeFormLocalFactor p j t := by
  unfold threeFormLocalFactor
  exact div_nonneg (sum_nonneg (fun b _ => sum_nonneg (fun c _ =>
    mul_nonneg (mul_nonneg (residueWeight_nonneg _ _ ht) (residueWeight_nonneg _ _ ht))
      (residueWeight_nonneg _ _ ht)))) (sq_nonneg _)

open Classical in
theorem three_form_local_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (θ : ℕ → ℝ) (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) {j : ℕ} (hj : j ≠ 0) :
    (∏ p ∈ P, threeFormLocalFactor p j (θ p)) ≤
      (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 3 * singularFactor 24 j := by
  have hlocal (p : ℕ) (hp : p ∈ P) : threeFormLocalFactor p j (θ p) ≤
      (1 - (1 - θ p) / p) ^ 3 * (if p ∣ j then 1 + 24 / (p : ℝ) else 1) := by
    let : Fact p.Prime := ⟨hP p hp⟩
    rw [threeFormLocalFactor_eq_mean]
    simpa only [ZMod.natCast_eq_zero_iff] using
      threeFormResidueMean_bound (j : ZMod p) (hθ p hp).1 (hθ p hp).2
  have hs (p : ℕ) (hp : p ∈ P) : 0 ≤ 1 - (1 - θ p) / p := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    have hp0 : (0 : ℝ) < p := by linarith
    apply sub_nonneg.mpr
    apply (div_le_one hp0).mpr
    linarith [(hθ p hp).1]
  have hexcept : (∏ p ∈ P, if p ∣ j then 1 + 24 / (p : ℝ) else 1) ≤
      singularFactor 24 j := by
    rw [← prod_filter]
    apply prod_le_prod_of_subset_of_one_le
    · intro p hp
      exact (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hj
    · intro p _
      positivity
    · intro p _ _
      exact le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ ∏ p ∈ P, (1 - (1 - θ p) / p) ^ 3 *
        (if p ∣ j then 1 + 24 / (p : ℝ) else 1) :=
      Finset.prod_le_prod (fun p hp => threeFormLocalFactor_nonneg p j (hθ p hp).1) hlocal
    _ = (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 3 *
        ∏ p ∈ P, if p ∣ j then 1 + 24 / (p : ℝ) else 1 := by
      rw [prod_mul_distrib, prod_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexcept (pow_nonneg (prod_nonneg hs) _)

/-- The actual three-form sieve, with a separated singular factor and
an explicit polynomial remainder. -/
theorem three_form_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (θ : ℕ → ℝ)
      (j u v w x Z : ℕ), j ≠ 0 → u ≤ v → w ≤ x → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 6 ≤ p) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ b ∈ Ico u v, ∑ c ∈ Ico w x, threeFormSieveWeight P θ j b c) ≤
        C * ((v : ℝ) - u) * ((x : ℝ) - w) *
          (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 3 * singularFactor 24 j +
        2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := affine_rectangle_sieve hFord hM (by norm_num : 0 < (3 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P θ j u v w x Z hj huv hwx hZ hP hθ
  classical
  let a : (p : P) → Fin 3 → ZMod p.val := fun _ => ![1, 0, 1]
  let b : (p : P) → Fin 3 → ZMod p.val := fun _ => ![0, 1, j]
  let c : (p : P) → Fin 3 → ZMod p.val := fun _ => ![0, 0, 0]
  let t : P → Fin 3 → ℝ := fun p _ => θ p.val
  have hproper (p : P) (i : Fin 3) : a p i ≠ 0 ∨ b p i ≠ 0 := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    fin_cases i <;> simp [a, b]
  have heq (p : P) (r s : ZMod p.val) :
      affineFormWeight (a p) (b p) (c p) (t p) r s =
        residueWeight (θ p.val) 0 r * residueWeight (θ p.val) 0 s *
          residueWeight (θ p.val) 0 (r + j * s) := by
    simp [affineFormWeight, a, b, c, t, Fin.prod_univ_succ, residueWeight, mul_assoc]
    split_ifs <;> rfl
  have hh := hbound P a b c t u v w x Z huv hwx hZ hP hproper (fun p _ => hθ p.val p.property)
  simp_rw [heq] at hh
  have hweight (r s : ℕ) : (∏ p : P, residueWeight (θ p.val) 0 (r : ZMod p.val) *
      residueWeight (θ p.val) 0 (s : ZMod p.val) *
        residueWeight (θ p.val) 0 ((r : ZMod p.val) + j * s)) = threeFormSieveWeight P θ j r s :=
    P.prod_coe_sort (fun p : ℕ => residueWeight (θ p) 0 (r : ZMod p) *
      residueWeight (θ p) 0 (s : ZMod p) * residueWeight (θ p) 0 ((r : ZMod p) + j * s))
  simp_rw [hweight] at hh
  change _ ≤ C * ((v : ℝ) - u) * ((x : ℝ) - w) *
    (∏ p : P, threeFormLocalFactor p.val j (θ p.val)) + _ at hh
  rw [P.prod_coe_sort (fun p : ℕ => threeFormLocalFactor p j (θ p))] at hh
  refine hh.trans (add_le_add ?_ le_rfl)
  have hprod := three_form_local_product_bound P (fun p hp => (hP p hp).1) θ hθ hj
  have harea : 0 ≤ C * ((v : ℝ) - u) * ((x : ℝ) - w) := by
    apply mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast huv)))
      (sub_nonneg.mpr (by exact_mod_cast hwx))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod harea

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CoefficientSieveMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Truncating the prime conditions majorizes the actual coefficients -/

namespace JointDickman

open Finset

theorem sievedCoefficientWeight_nonneg (P Z n : ℕ) : 0 ≤ sievedCoefficientWeight P Z n :=
  prod_nonneg (fun p _ => residueWeight_nonneg _ _ (roughSieveTheta_bounds P p).1)

theorem roughSquarefreeWeight_le_sieved (P Z n : ℕ) :
    roughSquarefreeWeight (Nat.primesLE P) (1 / 2) n ≤ sievedCoefficientWeight P Z n := by
  classical
  by_cases hd : Disjoint n.primeFactors (Nat.primesLE P)
  · by_cases hsq : Squarefree n
    · have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
        calc
          _ = ArithmeticFunction.cardFactors (∏ p ∈ n.primeFactors, p) :=
            congrArg ArithmeticFunction.cardFactors (Nat.prod_primeFactors_of_squarefree hsq).symm
          _ = _ := primeProduct_cardFactors _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
      have heq (p : ℕ) (hp : p ∈ sievePrimes Z) :
          residueWeight (roughSieveTheta P p) 0 (n : ZMod p) =
            if p ∣ n then (1 / 2 : ℝ) else 1 := by
        have hpprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        by_cases hpn : p ∣ n
        · have hpP : ¬ p ≤ P := by
            intro h
            exact disjoint_left.mp hd (hpprime.mem_primeFactors hpn hsq.ne_zero)
              (Nat.mem_primesLE.mpr ⟨h, hpprime⟩)
          simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn, roughSieveTheta, hpP]
        · simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn]
      have hsub : (sievePrimes Z).filter (fun p => p ∣ n) ⊆ n.primeFactors := by
        intro p hp
        have hmem := mem_filter.mp hp
        exact (Nat.mem_primesLE.mp (mem_filter.mp hmem.1).1).2.mem_primeFactors hmem.2 hsq.ne_zero
      have hsieve : sievedCoefficientWeight P Z n =
          (1 / 2 : ℝ) ^ ((sievePrimes Z).filter (fun p => p ∣ n)).card := by
        unfold sievedCoefficientWeight
        simp_rw [prod_congr rfl heq, ← prod_filter]
        simp
      rw [roughSquarefreeWeight, ArithmeticFunction.coe_mk, ite_eq_left hd,
        squarefreeWeight, ArithmeticFunction.coe_mk, ite_eq_left hsq, hcard, hsieve]
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (card_le_card hsub)
    · simpa [roughSquarefreeWeight, squarefreeWeight, hd, hsq] using sievedCoefficientWeight_nonneg P Z n
  · simpa [roughSquarefreeWeight, hd] using sievedCoefficientWeight_nonneg P Z n

theorem coefficientWeight_le_sieved (B Z n : ℕ) :
    coefficientWeight B n ≤ coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z n :=
  mul_le_mul_of_nonneg_left (roughSquarefreeWeight_le_sieved _ _ _) (coefficientScale_nonneg B)

theorem coefficient_triple_le_sieved (B Z j b c : ℕ) :
    coefficientWeight B b * coefficientWeight B c * coefficientWeight B (b + j * c) ≤
      coefficientScale B ^ 3 *
        threeFormSieveWeight (sievePrimes Z) (roughSieveTheta (auxiliaryCutoff B)) j b c := by
  have h := mul_le_mul
    (mul_le_mul (coefficientWeight_le_sieved B Z b) (coefficientWeight_le_sieved B Z c)
      (coefficientWeight_nonneg B c)
      (mul_nonneg (coefficientScale_nonneg B) (sievedCoefficientWeight_nonneg _ _ _)))
    (coefficientWeight_le_sieved B Z (b + j * c)) (coefficientWeight_nonneg B (b + j * c))
    (mul_nonneg (mul_nonneg (coefficientScale_nonneg B) (sievedCoefficientWeight_nonneg _ _ _))
      (mul_nonneg (coefficientScale_nonneg B) (sievedCoefficientWeight_nonneg _ _ _)))
  apply h.trans_eq
  simp only [sievedCoefficientWeight, threeFormSieveWeight, Nat.cast_add, Nat.cast_mul,
    prod_mul_distrib]
  ring

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

theorem inverseSelectedPrimeOdds_le {P z : ℝ} (hP : 0 < P)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hcut : ∀ p ∈ S, P ≤ p) :
    (∏ p ∈ S, (1 - z / (p : ℝ))⁻¹) ≤ Real.exp (2 * (S.card : ℝ) / P) := by
  have hx (p : ℕ) (hp : p ∈ S) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have hsum : (∑ p ∈ S, z / (p : ℝ)) ≤ (S.card : ℝ) / P := by
    calc
      _ ≤ ∑ _p ∈ S, 1 / P := sum_le_sum (fun p hp => by
        have hp0 : (0 : ℝ) < p := hP.trans_le (hcut p hp)
        exact (div_le_div_of_nonneg_right hz1 hp0.le).trans
          (one_div_le_one_div_of_le hP (hcut p hp)))
      _ = _ := by simp [div_eq_mul_inv]
  exact (inverse_product_le_exp S (fun p => z / (p : ℝ)) hx).trans
    (Real.exp_le_exp.mpr (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RectangleRemainder
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the explicit rectangular sieve remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem rectangle_remainder_bound {L H E F Z : ℝ} (hE : 0 < E)
    (hEL : E ≤ L) (hEH : E ≤ H) (hZ1 : 1 ≤ Z) (hZF : Z ≤ F) (hFE : F ≤ E) :
    2 * (L + H + 2 * Z) * (Z + 1) * Z ^ 3 ≤ 16 * L * H * F ^ 4 / E := by
  have hL : 0 ≤ L := hE.le.trans hEL
  have hH : 0 ≤ H := hE.le.trans hEH
  have hZ : 0 ≤ Z := by linarith
  have hF : 0 ≤ F := hZ.trans hZF
  have hELH : E * L ≤ L * H := by nlinarith [mul_le_mul_of_nonneg_left hEH hL]
  have hEHL : E * H ≤ L * H := mul_le_mul_of_nonneg_right hEL hH
  have hEZ : E * Z ≤ L * H := mul_le_mul hEL ((hZF.trans hFE).trans hEH) hZ hL
  have hlength : L + H + 2 * Z ≤ 4 * L * H / E := by
    apply (le_div_iff₀ hE).mpr
    nlinarith
  have hZF2 : Z + 1 ≤ 2 * F := by linarith
  calc
    _ ≤ 2 * (4 * L * H / E) * (2 * F) * F ^ 3 := by gcongr
    _ = _ := by ring

theorem coefficient_rectangle_remainder_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, ∀ L H : ℝ,
      Real.exp (δ * B) ≤ L → Real.exp (δ * B) ≤ H →
      coefficientScale B ^ 3 *
        (2 * (L + H + 2 * sieveCutoff (δ / 8) B) *
          (sieveCutoff (δ / 8) B + 1 : ℝ) * (sieveCutoff (δ / 8) B : ℝ) ^ 3) ≤ L * H := by
  have hlim : Tendsto (fun B : ℕ => 16 * ((B : ℝ) ^ 3 /
      Real.exp ((δ / 2) * B))) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 3 (by linarith : 0 < δ / 2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, mul_zero] using
      (h.comp tendsto_natCast_atTop_atTop).const_mul 16
  have hsmall := hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, coefficientScale_eventually_le,
    sieveCutoff_eventually (by linarith : 0 < δ / 8)]
    with B hsmallB hscale hcut
  intro L H hL hH
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hF : Real.exp ((δ / 8) * B) ≤ Real.exp (δ * B) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hz1 : (1 : ℝ) ≤ sieveCutoff (δ / 8) B := by exact_mod_cast (by omega : 1 ≤ sieveCutoff (δ / 8) B)
  have hbound := rectangle_remainder_bound (Real.exp_pos _) hL hH hz1 hcut.2.2.2 hF
  have heq : Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B) =
      (Real.exp ((δ / 2) * B))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_neg]
    congr 1
    ring
  have hLH : 0 ≤ L * H := mul_nonneg ((Real.exp_pos _).le.trans hL)
    ((Real.exp_pos _).le.trans hH)
  have hL0 : 0 ≤ L := (Real.exp_pos _).le.trans hL
  have hH0 : 0 ≤ H := (Real.exp_pos _).le.trans hH
  calc
    _ ≤ (B : ℝ) ^ 3 * (16 * L * H * Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B)) :=
      mul_le_mul (pow_le_pow_left₀ (coefficientScale_nonneg B) hscale 3) hbound
        (by positivity) (pow_nonneg hB0 _)
    _ = (16 * ((B : ℝ) ^ 3 / Real.exp ((δ / 2) * B))) * (L * H) := by
      calc
        _ = 16 * (B : ℝ) ^ 3 * (Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B)) * (L * H) := by ring
        _ = _ := by rw [heq]; ring
    _ ≤ 1 * (L * H) := mul_le_mul_of_nonneg_right hsmallB hLH
    _ = _ := one_mul _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IndependentRegularityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity loss for two independent coefficient weights -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem regularCoefficientWeight_le (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    regularCoefficientWeight B L τ C n ≤ coefficientWeight B n := by
  unfold regularCoefficientWeight
  split_ifs
  · exact le_rfl
  · exact coefficientWeight_nonneg B n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDyadicBoxes
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic boxes covering the amplification coefficients -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientDyadicBox_disjoint (T : ℕ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (coefficientDyadicBox T k) (coefficientDyadicBox T l) := by
  have hforward : ∀ k l : ℕ, k < l →
      Disjoint (coefficientDyadicBox T k) (coefficientDyadicBox T l) := by
    intro k l hlt
    apply disjoint_left.mpr
    intro ac hk hl
    have hkc := mem_Ico.mp (mem_product.mp hk).2
    have hlc := mem_Ico.mp (mem_product.mp hl).2
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hlt
    rw [pow_succ, mul_comm _ 2] at hpow
    omega
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hforward k l h
  · exact (hforward l k h).symm

theorem nat_two_pow_exp (k : ℕ) :
    ((2^k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_cast

theorem coefficientDyadicCover_contains {B T a c : ℕ} (hB : 0 < B)
    (hcl : Real.exp (B : ℝ) ≤ c) (hcu : (c : ℝ) ≤ Real.exp (2 * B))
    (ha : T * c ≤ a) (ha' : a < 2 * T * c) :
    (a, c) ∈ coefficientDyadicCover B T := by
  have hc0 : 0 < c := by exact_mod_cast (Real.exp_pos (B : ℝ)).trans_le hcl
  have hcne : c ≠ 0 := Nat.ne_of_gt hc0
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlo : B ≤ Nat.log 2 c := by
    apply (Nat.le_log_iff_pow_le (by norm_num) hcne).mpr
    have hpow : ((2^B : ℕ) : ℝ) ≤ c := by
      rw [nat_two_pow_exp]
      apply le_trans (Real.exp_le_exp.mpr _) hcl
      nlinarith only [Real.log_two_lt_d9]
    exact_mod_cast hpow
  have hhi : Nat.log 2 c < 4 * B := by
    apply (Nat.log_lt_iff_lt_pow (by norm_num) hcne).mpr
    have hpow : (c : ℝ) < ((2^(4 * B) : ℕ) : ℝ) := by
      rw [nat_two_pow_exp]
      apply lt_of_le_of_lt hcu
      apply Real.exp_lt_exp.mpr
      push_cast
      nlinarith only [Real.log_two_gt_d9, hB0]
    exact_mod_cast hpow
  have hcp := Nat.pow_log_le_self 2 hcne
  have hcp' := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) c
  rw [pow_succ, mul_comm _ 2] at hcp'
  apply mem_biUnion.mpr
  refine ⟨Nat.log 2 c, mem_Ico.mpr ⟨hlo, hhi⟩, ?_⟩
  apply mem_product.mpr
  constructor
  · apply mem_Ico.mpr
    constructor
    · exact (Nat.mul_le_mul_left T hcp).trans ha
    · have hh := Nat.mul_le_mul_left (2 * T) hcp'.le
      nlinarith only [ha', hh]
  · exact mem_Ico.mpr ⟨hcp, hcp'⟩

theorem mem_amplificationCoefficientPairs {B T a c : ℕ} (hB : 0 < B) :
    (a, c) ∈ amplificationCoefficientPairs B T ↔
      Real.exp (B : ℝ) ≤ c ∧ (c : ℝ) ≤ Real.exp (2 * B) ∧
        T * c ≤ a ∧ a < 2 * T * c := by
  classical
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨coefficientDyadicCover_contains hB h.1 h.2.1 h.2.2.1 h.2.2.2, h⟩

/-- Every box in the cover is long enough for the sieve and remains
inside the coefficient range of the local prime-product law. -/
theorem coefficientDyadicBox_scales :
    ∀ᶠ B : ℕ in atTop, ∀ T k : ℕ, (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      k ∈ Ico B (4 * B) →
      Real.exp ((1 / 2 : ℝ) * B) ≤ ((2^k : ℕ) : ℝ) ∧
        (4 * T * (2^k : ℕ) : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
  have hexp : ∀ᶠ B : ℕ in atTop, (4 : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 10))).eventually_ge_atTop 4
  filter_upwards [hexp, eventually_gt_atTop 0] with B h4 hB
  intro T k hT hk
  have hk' := mem_Ico.mp hk
  have hklo : (B : ℝ) ≤ k := by exact_mod_cast hk'.1
  have hkhi : (k : ℝ) ≤ 4 * B := by exact_mod_cast hk'.2.le
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlog0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : Real.exp ((1 / 2 : ℝ) * B) ≤ ((2^k : ℕ) : ℝ) := by
    rw [nat_two_pow_exp]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hklo hlog0.le
    nlinarith only [hh, Real.log_two_gt_d9, hB0]
  have hhigh : ((2^k : ℕ) : ℝ) ≤ Real.exp ((14 / 5 : ℝ) * B) := by
    rw [nat_two_pow_exp]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hkhi hlog0.le
    nlinarith only [hh, Real.log_two_lt_d9, hB0]
  refine ⟨hlow, ?_⟩
  calc
    (4 * T * (2^k : ℕ) : ℝ) ≤
        Real.exp ((1 / 10 : ℝ) * B) * Real.exp ((1 / 10 : ℝ) * B) * Real.exp ((14 / 5 : ℝ) * B) := by
      gcongr
    _ = Real.exp (3 * (B : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((16 / 5 : ℝ) * B) := Real.exp_le_exp.mpr (by linarith only [hB0])

theorem amplificationCoefficientPairs_size :
    ∀ᶠ B : ℕ in atTop, ∀ T a c : ℕ, 0 < T →
      (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (a, c) ∈ amplificationCoefficientPairs B T →
      (a : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) ∧
        (c : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
  classical
  filter_upwards [coefficientDyadicBox_scales] with B hs
  intro T a c hT hTsize hac
  obtain ⟨k, hk, hbox⟩ := mem_biUnion.mp (mem_filter.mp hac).1
  have hscale := (hs T k hTsize hk).2
  obtain ⟨ha, hc⟩ := mem_product.mp hbox
  have ha' : (a : ℝ) ≤ 4 * T * (2^k : ℕ) := by exact_mod_cast (mem_Ico.mp ha).2.le
  have hc' : (c : ℝ) ≤ 2 * (2^k : ℕ) := by exact_mod_cast (mem_Ico.mp hc).2.le
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  refine ⟨ha'.trans hscale, hc'.trans (le_trans ?_ hscale)⟩
  have hh := mul_le_mul_of_nonneg_right hT1 (by positivity : (0 : ℝ) ≤ (2^k : ℕ))
  nlinarith only [hh, show (0 : ℝ) ≤ (2^k : ℕ) by positivity]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AmplificationSmoothCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

open Classical in
theorem amplificationSmoothWeight_support {B T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (a c : ℕ) (h : (a,c) ∉ amplificationCoefficientPairs B T) :
    amplificationSmoothWeight B T a c = 0 := by
  by_contra hn
  have hs := mul_ne_zero_iff.mp hn
  obtain ⟨hcl,hcu⟩ := amplificationBump_support hs.1
  obtain ⟨hal,hau⟩ := amplificationBump_support hs.2
  have hc : 0 < c := by
    by_contra hc
    have hz : c = 0 := by omega
    subst c
    norm_num at hcl
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTC0 := mul_pos hT0 hc0
  apply h
  apply (mem_amplificationCoefficientPairs hB).mpr
  have hcl' : (B : ℝ) < Real.log c := by
    have hh := (lt_div_iff₀ hB0).mp hcl
    simpa only [one_mul] using hh
  have hcu' := (div_lt_iff₀ hB0).mp hcu
  have hal' := (lt_div_iff₀ hTC0).mp hal
  have hau' := (div_lt_iff₀ hTC0).mp hau
  refine ⟨?_,?_,?_,?_⟩
  · exact (Real.exp_le_exp.mpr hcl'.le).trans_eq (Real.exp_log hc0)
  · exact (Real.exp_log hc0).symm.trans_le (Real.exp_le_exp.mpr hcu'.le)
  · exact_mod_cast (by simpa only [one_mul] using hal'.le : (T : ℝ)*c ≤ a)
  · have hh : (a : ℝ) < (2*T*c : ℕ) := by push_cast; nlinarith only [hau']
    exact_mod_cast hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_RealPeriodicMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real moments of a fixed finite-period function -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem real_periodic_moment_tendsto {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (f n)^k) / (N : ℝ))
      atTop (nhds ((∑ a : ZMod q, (f a)^k) / (q : ℝ))) := by
  have h := periodicAverage_tendsto (fun a => (((f a)^k : ℝ) : ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, periodicAverage, residueMean,
    Complex.div_natCast_re, Complex.re_sum, Complex.ofReal_re] using hr

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationVolumeProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient harmonic mass cancels the residue-weight mean -/

namespace JointDickman
open Finset

theorem baseArithmeticResidueWeight_product (B n : ℕ) :
    baseArithmeticResidueWeight B n = auxiliaryRatio B ^ (1/2 : ℝ) *
      ∏ p ∈ auxiliaryPrimes B, if p ∣ n then (1/2 : ℝ) else 1 := by
  unfold baseArithmeticResidueWeight residueBaseWeight coefficientPrimeSet
  rw [← prod_const, prod_filter]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActiveVolumeMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A periodic majorant for the active Cauchy volume -/

namespace JointDickman
open Finset

theorem baseArithmeticResidueWeight_nonneg (B n : ℕ) : 0 ≤ baseArithmeticResidueWeight B n := by
  unfold baseArithmeticResidueWeight residueBaseWeight
  exact mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _) (by positivity)

theorem arithmeticResidueWeight_le_base (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    arithmeticResidueWeight B L τ C n ≤ baseArithmeticResidueWeight B n := by
  unfold arithmeticResidueWeight regularResidueWeight baseArithmeticResidueWeight
  split_ifs
  · rfl
  · exact baseArithmeticResidueWeight_nonneg B n

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithGraph
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact arithmetic reindexing in the divisor graph

The change of variables turns two divisor representations into an additive
edge. The underlying integer identities hold in both directions without
asymptotic hypotheses.
-/

namespace JointDickman

/-- Reconstruct the second quotient and the additive edge from the first
quotient. All variables are integers, allowing both signs of the lag. -/
theorem divisor_edge_forward {a b c j m z : ℤ}
    (hcoeff : a - b = j * c) (hquot : c * z = a * m + 1) :
    c * (z - j * m) = b * m + 1 ∧
      b * z + j = a * (z - j * m) := by
  constructor
  · linear_combination hquot + m * hcoeff
  · linear_combination -z * hcoeff - j * hquot

/-- The congruence at the new endpoint reconstructs the old divisor
representation. Coprimality with the lag is precisely the cancellation
needed in the reverse direction. -/
theorem divisor_edge_iff {a b c j z : ℤ}
    (hcoeff : a - b = j * c) (hcop : IsCoprime a j) :
    (∃ m : ℤ, c * z = a * m + 1) ↔ a ∣ b * z + j := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨z - j * m, (divisor_edge_forward hcoeff hm).2⟩
  · rintro ⟨k, hk⟩
    have hdiv : a ∣ j * (c * z - 1) := by
      refine ⟨z - k, ?_⟩
      linear_combination -z * hcoeff - hk
    obtain ⟨m, hm⟩ := hcop.dvd_of_dvd_mul_left hdiv
    exact ⟨m, by linarith⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorGraphSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic support of the unequal-coefficient graph edges -/

namespace JointDickman
open Finset

theorem coprime_of_divisor_linear_succ {a c m : ℕ} (h : c ∣ a*m+1) :
    a.Coprime c ∧ m.Coprime c := by
  have ha : a.Coprime (a*m+1) :=
    (Nat.coprime_mul_left_add_right a 1 m).mpr (Nat.coprime_one_right a)
  have hm : m.Coprime (a*m+1) :=
    (Nat.coprime_mul_right_add_right m 1 a).mpr (Nat.coprime_one_right m)
  exact ⟨ha.coprime_dvd_right h, hm.coprime_dvd_right h⟩

theorem amplificationInnerWeight_support {T a c : ℕ}
    (h : amplificationInnerWeight T a c ≠ 0) :
    T*c < a ∧ a < 2*(T*c) := by
  have hs := amplificationBump_support h
  have hd : T*c ≠ 0 := by
    intro he
    have hz : (T : ℝ)*(c : ℝ) = 0 := by exact_mod_cast he
    simp only [amplificationInnerWeight, hz, div_zero] at h
    exact h (amplificationBump_zero (Or.inl (by norm_num)))
  have hp : (0 : ℝ) < (T : ℝ)*c := by exact_mod_cast Nat.pos_of_ne_zero hd
  constructor
  · have hl : (T : ℝ)*c < a := by simpa only [one_mul] using (lt_div_iff₀ hp).mp hs.1
    exact_mod_cast hl
  · exact_mod_cast (div_lt_iff₀ hp).mp hs.2

/-- Once the coefficient is coprime to the lag and to c, the edge's two
coefficients are coprime. This is the cancellation used by the inverse map. -/
theorem divisor_edge_coprime {a b c : ℕ} {j : ℤ}
    (hac : a.Coprime c) (haj : a.Coprime j.natAbs)
    (he : (a : ℤ)-b = j*c) : a.Coprime b := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpb
  have hpjc : (p : ℤ) ∣ j*c := by
    rw [← he]
    exact dvd_sub (by exact_mod_cast hpa) (by exact_mod_cast hpb)
  have hpjc' : p ∣ j.natAbs*c := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natCast_dvd.mp hpjc
  have hpj : p ∣ j.natAbs := (hac.coprime_dvd_left hpa).dvd_mul_right.mp hpjc'
  exact Nat.dvd_one.mpr (Nat.eq_one_of_dvd_coprimes haj hpa hpj)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NonzeroGraphAtoms
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero summands give genuine coprime small-lag graph edges -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- The prescribed multiplier is eventually below the lower prime cutoff. -/
theorem amplificationMultiplier_le_cutoff : ∀ᶠ B : ℕ in atTop,
    amplificationMultiplier B ≤ auxiliaryCutoff B := by
  filter_upwards [amplificationMultiplier_comparable,eventually_ge_atTop 1] with B hT hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : (B : ℝ)^(8/25 : ℝ) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hBr (by norm_num : (8/25 : ℝ) ≤ 1)
  have hTB : amplificationMultiplier B ≤ B := by exact_mod_cast hT.2.2.trans hpow
  have hbpow : B ≤ B ^ (1000 : ℕ) := le_self_pow₀ hB (by decide : (1000 : ℕ) ≠ 0)
  exact hTB.trans hbpow

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorEdgeEndpoints
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer endpoints of a divisor-graph edge -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Forward reindexing at the actual natural quotients, for either sign
of the lag. The shifted endpoint is positive automatically. -/
theorem natural_divisor_edge_endpoints {a b c m : ℕ} {j : ℤ}
    (hc : 0 < c) (ha : c ∣ a*m+1) (hb : c ∣ b*m+1)
    (he : (a : ℤ)-b = j*c) :
    ((b*((a*m+1)/c) : ℕ) : ℤ)+j = ((a*((b*m+1)/c) : ℕ) : ℤ) := by
  have hqa : (c : ℤ)*((a*m+1)/c : ℕ) = (a : ℤ)*m+1 := by
    exact_mod_cast Nat.mul_div_cancel' ha
  have hqb : (c : ℤ)*((b*m+1)/c : ℕ) = (b : ℤ)*m+1 := by
    exact_mod_cast Nat.mul_div_cancel' hb
  change (b : ℤ)*(((a*m+1)/c : ℕ) : ℤ)+j =
    (a : ℤ)*(((b*m+1)/c : ℕ) : ℤ)
  apply mul_left_cancel₀ (show (c : ℤ) ≠ 0 by exact_mod_cast (ne_of_gt hc))
  linear_combination (b : ℤ)*hqa - (a : ℤ)*hqb - he

/-- The inverse congruence reconstructs a nonnegative multiplier. It uses
only coprimality with the lag and positivity of the endpoint. -/
theorem natural_divisor_edge_inverse {a b c n : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (hn : 0 < n) (hb : b ∣ n)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (hdiv : (a : ℤ) ∣ (n : ℤ)+j) :
    ∃! m : ℕ, c*(n/b) = a*m+1 := by
  have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb hn
  have hnb : b*(n/b) = n := Nat.mul_div_cancel' hb
  have hcop' : IsCoprime (a : ℤ) j := by
    have h := hcop.isCoprime
    exact h.of_isCoprime_of_dvd_right Int.dvd_natAbs_self
  have hd' : (a : ℤ) ∣ (b : ℤ)*((n/b : ℕ) : ℤ)+j := by
    have hid : (b : ℤ)*((n/b : ℕ) : ℤ) = n := by exact_mod_cast hnb
    rwa [hid]
  obtain ⟨m,hm⟩ := (divisor_edge_iff he hcop').mpr hd'
  have hnq : 0 < n/b := Nat.div_pos (Nat.le_of_dvd hn hb) hb0
  have hmul : 0 ≤ (a : ℤ)*m := by
    have hcz : (1 : ℤ) ≤ (c : ℤ)*((n/b : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_pos hc hnq
    linarith
  have hm0 : 0 ≤ m := nonneg_of_mul_nonneg_right hmul (by exact_mod_cast ha)
  refine ⟨m.toNat,?_,?_⟩
  · have heq : (c : ℤ)*((n/b : ℕ) : ℤ) = (a : ℤ)*(m.toNat : ℤ)+1 := by
      simpa only [Int.toNat_of_nonneg hm0] using hm
    exact_mod_cast heq
  · intro m' hm'
    apply Nat.eq_of_mul_eq_mul_left ha
    have hmnat : c*(n/b) = a*m.toNat+1 := by
      have heq : (c : ℤ)*((n/b : ℕ) : ℤ) = (a : ℤ)*(m.toNat : ℤ)+1 := by
        simpa only [Int.toNat_of_nonneg hm0] using hm
      exact_mod_cast heq
    omega

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorEdgeReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite transport from multiplier sums to additive graph endpoints -/

namespace JointDickman
open Finset

theorem divisorEdgeInverse_eq {a b c n m : ℕ} (ha : 0 < a)
    (h : c*(n/b) = a*m+1) : divisorEdgeInverse a b c n = m := by
  unfold divisorEdgeInverse
  rw [h,Nat.add_sub_cancel,Nat.mul_div_cancel_left m ha]

/-- Every allowed endpoint reconstructs one old multiplier. -/
theorem divisorEdge_inverse_mem {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (he : (a : ℤ)-b = j*c)
    (hcop : a.Coprime j.natAbs) {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    divisorEdgeInverse a b c n ∈ divisorEdgeOld a b c N ∧
      b*((a*divisorEdgeInverse a b c n+1)/c) = n := by
  classical
  obtain ⟨hnrange,hbn,hd,ham,hbm⟩ := mem_filter.mp hn
  have hn0 : 0 < n := (mem_Icc.mp hnrange).1
  obtain ⟨m,hm,_⟩ := natural_divisor_edge_inverse ha hc hn0 hbn he hcop hd
  have hinv : divisorEdgeInverse a b c n = m := divisorEdgeInverse_eq ha hm
  have hca : c ∣ a*m+1 := by rw [← hm]; exact dvd_mul_right c (n/b)
  have hcb : c ∣ b*m+1 := by
    have hdiff : (c : ℤ) ∣ (a : ℤ)-b := ⟨j,by simpa only [mul_comm] using he⟩
    have hx : (c : ℤ) ∣ (a : ℤ)*m+1 := by exact_mod_cast hca
    have hy := dvd_sub hx (dvd_mul_of_dvd_left hdiff (m : ℤ))
    have hz : (a : ℤ)*m+1-((a : ℤ)-b)*m = (b : ℤ)*m+1 := by ring
    rw [hz] at hy
    exact_mod_cast hy
  have hmN : m < N := by
    rw [hinv] at ham
    exact (Nat.le_mul_of_pos_left m ha).trans_lt ham
  rw [hinv]
  refine ⟨mem_filter.mpr ⟨mem_range.mpr hmN,?_,?_,?_,?_⟩,?_⟩
  · simpa only [hinv] using ham
  · simpa only [hinv] using hbm
  · simpa only [hinv] using hca
  · simpa only [hinv] using hcb
  · rw [← hm,Nat.mul_div_cancel_left _ hc]
    exact Nat.mul_div_cancel' hbn

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphPair
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic graph weight obtained from the actual quadratic form -/

namespace JointDickman
open Finset

theorem divisorEdge_new_quotients {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    (a*divisorEdgeInverse a b c n+1)/c = n/b ∧
      (b*divisorEdgeInverse a b c n+1)/c = ((n : ℤ)+j).toNat/a := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨_,_,_,hca,hcb⟩ := mem_filter.mp hm
  constructor
  · calc
      _ = (b*((a*divisorEdgeInverse a b c n+1)/c))/b :=
        (Nat.mul_div_cancel_left _ hb).symm
      _ = n/b := congrArg (fun t => t/b) hback
  · have hend : (n : ℤ)+j = ((a*((b*divisorEdgeInverse a b c n+1)/c) : ℕ) : ℤ) := by
      have h := natural_divisor_edge_endpoints hc hca hcb he
      rwa [hback] at h
    rw [hend,Int.toNat_natCast,Nat.mul_div_cancel_left _ ha]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteGraphRegroup
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite regrouping by graph lag and vertex -/

namespace JointDickman
open Finset

theorem finite_graph_regroup {ι κ ν : Type*} [DecidableEq κ] [DecidableEq ν]
    (s : Finset ι) (t : Finset κ) (v : Finset ν) (lag : ι → κ)
    (edge : ι → Finset ν) (w : ι → ν → ℝ) (h : κ → ν → ℝ)
    (hlag : ∀ i ∈ s, lag i ∈ t) (hedge : ∀ i ∈ s, edge i ⊆ v) :
    (∑ i ∈ s, ∑ n ∈ edge i, w i n * h (lag i) n) =
      ∑ n ∈ v, ∑ j ∈ t, (∑ i ∈ s, if lag i = j ∧ n ∈ edge i then w i n else 0) * h j n := by
  symm
  simp_rw [sum_mul]
  calc
    _ = ∑ n ∈ v, ∑ i ∈ s, ∑ j ∈ t,
        (if lag i = j ∧ n ∈ edge i then w i n else 0) * h j n := by
      apply sum_congr rfl
      intro n _
      rw [sum_comm]
    _ = ∑ i ∈ s, ∑ n ∈ v, ∑ j ∈ t,
        (if lag i = j ∧ n ∈ edge i then w i n else 0) * h j n := by rw [sum_comm]
    _ = ∑ i ∈ s, ∑ n ∈ v, if n ∈ edge i then w i n * h (lag i) n else 0 := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro n _
      by_cases hn : n ∈ edge i
      · simp only [hn,and_true,ite_mul,zero_mul]
        simp [hlag i hi]
      · simp [hn]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      calc
        _ = ∑ n ∈ edge i, if n ∈ edge i then w i n * h (lag i) n else 0 := by
          apply (sum_subset (hedge i hi) _).symm
          intro n _ hn
          simp [hn]
        _ = _ := sum_congr rfl (fun n hn => by simp [hn])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticGraphKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual arithmetic graph by lag and endpoint -/

namespace JointDickman
open Finset

theorem graphTriple_lag_mem {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) : graphTripleLag i ∈ Icc (-(T : ℤ)) T := by
  classical
  have hg := (mem_filter.mp hi).2
  have hlt : |graphTripleLag i| < (T : ℤ) := by
    change |coefficientPairLag i.1 i.2.1 i.2.2| < (T : ℤ)
    rw [← Int.natCast_natAbs]
    exact_mod_cast hg.2.2.1
  exact mem_Icc.mpr ⟨(abs_lt.mp hlt).1.le,(abs_lt.mp hlt).2.le⟩

theorem graphTriple_edges_subset {B T N : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    graphTripleEdges N i ⊆ Icc 1 (arithmeticGraphVertexCap B N) := by
  classical
  intro n hn
  have hE := mem_powerset.mp (mem_product.mp (mem_product.mp (mem_filter.mp hi).1).2).2
  have hb : (∏ p ∈ i.2.2, p) ∣ ∏ p ∈ auxiliaryPrimes B, p :=
    prod_dvd_prod_of_subset _ _ id hE
  have hp : 0 < ∏ p ∈ auxiliaryPrimes B, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p hp).pos)
  have hb_le := Nat.le_of_dvd hp hb
  have hn' := mem_Icc.mp (mem_filter.mp hn).1
  exact mem_Icc.mpr ⟨hn'.1,hn'.2.trans (Nat.mul_le_mul_right N hb_le)⟩

theorem arithmeticOffDiagonalGraph_triples (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) :
    arithmeticOffDiagonalGraph B L τ C T N F =
      (∑ i ∈ arithmeticGraphTriples B T, ∑ n ∈ graphTripleEdges N i,
        graphTripleWeight B L τ C T i n * (star (F n)*F ((n : ℤ)+graphTripleLag i).toNat).re)/(N : ℝ) := by
  classical
  unfold arithmeticOffDiagonalGraph arithmeticGraphTriples
  rw [sum_filter,sum_product]
  congr 1
  apply sum_congr rfl
  intro D _
  rw [sum_product]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro E _
  rfl

/-- The graph form as a sum of one kernel per small additive lag. This
identity precedes all kernel estimates and contains no analytic premise. -/
theorem arithmeticOffDiagonalGraph_kernel (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) :
    arithmeticOffDiagonalGraph B L τ C T N F =
      (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N), ∑ j ∈ Icc (-(T : ℤ)) T,
        rawArithmeticGraphKernel B L τ C T N j n * (star (F n)*F ((n : ℤ)+j).toNat).re)/(N : ℝ) := by
  rw [arithmeticOffDiagonalGraph_triples]
  congr 1
  exact finite_graph_regroup (arithmeticGraphTriples B T) (Icc (-(T : ℤ)) T)
    (Icc 1 (arithmeticGraphVertexCap B N)) graphTripleLag (graphTripleEdges N)
    (graphTripleWeight B L τ C T) (fun j n => (star (F n)*F ((n : ℤ)+j).toNat).re)
    (fun _ hi => graphTriple_lag_mem hi) (fun _ hi => graphTriple_edges_subset hi)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positivity and support of the actual arithmetic graph kernel -/

namespace JointDickman
open Finset

theorem arithmeticGraphPairWeight_nonneg (B L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (hu : ∀ c, 0 ≤ u c)
    (hv : ∀ a c, 0 ≤ v a c) (a b c : ℕ) (j : ℤ) (n : ℕ) :
    0 ≤ arithmeticGraphPairWeight B L τ C u v a b c j n := by
  have hA (d l : ℕ) : 0 ≤ regularCoefficientWeight B L τ C d *
      arithmeticResidueWeight B L τ C l * v d c :=
    mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg B L τ C d)
      (regularResidueWeight_nonneg B L τ C _)) (hv d c)
  have hC : 0 ≤ u c * regularCoefficientWeight B L τ C c *
      arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n) :=
    mul_nonneg (mul_nonneg (hu c) (regularCoefficientWeight_nonneg B L τ C c))
      (regularResidueWeight_nonneg B L τ C _)
  exact mul_nonneg (mul_nonneg hC (hA a (n/b))) (hA b (((n : ℤ)+j).toNat/a))

theorem rawArithmeticGraphKernel_nonneg (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (j : ℤ) (n : ℕ) : 0 ≤ rawArithmeticGraphKernel B L τ C T N j n := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs
  · exact arithmeticGraphPairWeight_nonneg B L τ C (amplificationOuterWeight B)
      (amplificationInnerWeight T) (fun _ => (amplificationBump_bounds _).1)
      (fun _ _ => (amplificationBump_bounds _).1) _ _ _ _ _
  · rfl

theorem rawArithmeticGraphKernel_zero_lag (B L : ℕ) (τ C : ℝ) (T N n : ℕ) :
    rawArithmeticGraphKernel B L τ C T N 0 n = 0 := by
  classical
  apply sum_eq_zero
  intro i hi
  have hne := (mem_filter.mp hi).2.2.1
  change coefficientPairLag i.1 i.2.1 i.2.2 ≠ 0 at hne
  have hn : ¬ (graphTripleLag i = 0 ∧ n ∈ graphTripleEdges N i) := fun h => hne h.1
  exact ite_eq_right hn

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GraphResidueFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three distinct residue roots in a graph representation -/

namespace JointDickman
open Finset

open Classical in
theorem sum_three_residueWeights {α : Type*} [Fintype α]
    (t u v : ℝ) (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ x : α, residueWeight t a x * residueWeight u b x * residueWeight v c x =
      (Fintype.card α : ℝ) - 3 + t + u + v := by
  have he (x : α) :
      residueWeight t a x * residueWeight u b x * residueWeight v c x =
        1 + (if x = a then t-1 else 0) + (if x = b then u-1 else 0) +
          (if x = c then v-1 else 0) := by
    by_cases ha : x = a
    · subst x
      simp [residueWeight, hab, hac]
    · by_cases hb : x = b
      · subst x
        simp [residueWeight, Ne.symm hab, hbc]
      · by_cases hc : x = c
        · subst x
          simp [residueWeight, Ne.symm hac, Ne.symm hbc]
        · simp [residueWeight, ha, hb, hc]
  simp_rw [he]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    sum_ite_eq', mem_univ, ite_true, if_true]
  ring

theorem graph_three_root_mean {p : ℕ} [NeZero p] (a b c : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ x : ZMod p, residueWeight (1/2) a x * residueWeight (1/2) b x *
      residueWeight (1/2) c x) / (p : ℝ) = 1 - 3/(2*(p : ℝ)) := by
  rw [sum_three_residueWeights _ _ _ a b c hab hac hbc, ZMod.card]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp
  ring

/-- Product residue tests factor exactly, including nonnormalized tests. -/
theorem crt_product_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)]
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ) :
    (∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i))) /
      (∏ i, (m i : ℝ)) = ∏ i, (∑ x : ZMod (m i), f i x) / (m i : ℝ) := by
  rw [crt_period_sum m (fun i => NeZero.pos (m i)) hcop f, prod_div_distrib]

/-- At good primes the three graph roots are `0`, `-j`, and `b/c`. -/
theorem graph_roots_distinct {p : ℕ} [Fact p.Prime]
    (a b c j : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hj : j ≠ 0) (he : a = b+j*c) :
    (0 : ZMod p) ≠ -j ∧ (0 : ZMod p) ≠ b/c ∧ -j ≠ b/c := by
  refine ⟨by simpa using hj, Ne.symm (div_ne_zero hb hc), ?_⟩
  intro h
  have hmul : -j*c = b := (eq_div_iff hc).mp h
  apply ha
  rw [he, ← hmul]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GraphResidueMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing coefficient primes from the three quotient weights -/

namespace JointDickman
open Finset

theorem graph_residue_product {K : Type*} [Field K]
    (a b c j m l₁ l₂ n : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hn : n = b*l₁) (hj : n+j = a*l₂) (hm : c*n = a*b*m+b) :
    residueWeight (1/2) 0 m * residueWeight (1/2) 0 l₁ * residueWeight (1/2) 0 l₂ =
      residueWeight (1/2) 0 n * residueWeight (1/2) (-j) n *
        residueWeight (1/2) (b/c) n := by
  classical
  have h₁ : l₁ = 0 ↔ n = 0 := by
    rw [hn, mul_eq_zero]
    simp [hb]
  have h₂ : l₂ = 0 ↔ n = -j := by
    rw [← add_eq_zero_iff_eq_neg, hj, mul_eq_zero]
    simp [ha]
  have h₃ : m = 0 ↔ n = b/c := by
    rw [eq_div_iff hc]
    constructor
    · intro h
      rw [h, mul_zero, zero_add] at hm
      simpa only [mul_comm] using hm
    · intro h
      have hz : a*b*m = 0 := by linear_combination -hm + h
      exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero ha hb)
  simp only [residueWeight, h₁, h₂, h₃]
  ring

open Classical in
theorem base_residue_three_subset_le (B : ℕ) (G : Finset ℕ)
    (hG : G ⊆ auxiliaryPrimes B) (m l₁ l₂ : ℕ) :
    baseArithmeticResidueWeight B m * baseArithmeticResidueWeight B l₁ *
      baseArithmeticResidueWeight B l₂ ≤
    (auxiliaryRatio B ^ (1/2 : ℝ))^3 *
      ∏ p ∈ G, (if p ∣ m then (1/2 : ℝ) else 1) *
        (if p ∣ l₁ then (1/2 : ℝ) else 1) *
        (if p ∣ l₂ then (1/2 : ℝ) else 1) := by
  let f (p : ℕ) := (if p ∣ m then (1/2 : ℝ) else 1) *
    (if p ∣ l₁ then (1/2 : ℝ) else 1) * (if p ∣ l₂ then (1/2 : ℝ) else 1)
  have hf0 (p : ℕ) : 0 ≤ f p := by dsimp [f] <;> positivity
  have hf1 (p : ℕ) : f p ≤ 1 := by
    dsimp [f]
    split_ifs <;> norm_num
  have he : baseArithmeticResidueWeight B m * baseArithmeticResidueWeight B l₁ *
      baseArithmeticResidueWeight B l₂ =
      (auxiliaryRatio B ^ (1/2 : ℝ))^3 * ∏ p ∈ auxiliaryPrimes B, f p := by
    simp only [baseArithmeticResidueWeight_product, f, prod_mul_distrib]
    ring
  rw [he]
  have hR : 0 ≤ auxiliaryRatio B := by unfold auxiliaryRatio; positivity
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.rpow_nonneg hR _) _)
  exact prod_le_prod_of_subset_of_le_one hG (fun p _ => hf0 p) (fun p _ _ => hf1 p)

open Classical in
/-- An exact congruence calculation turns the retained quotient factors
into the three distinct roots used in the edge-mass calculation. -/
theorem graph_quotient_residue_majorant (B : ℕ) (G : Finset ℕ)
    (hG : G ⊆ auxiliaryPrimes B) (a b c m l₁ l₂ n : ℕ) (j : ℤ)
    (ha : ∀ p ∈ G, ¬ p ∣ a) (hb : ∀ p ∈ G, ¬ p ∣ b) (hc : ∀ p ∈ G, ¬ p ∣ c)
    (hn : n = b*l₁) (hj : (n : ℤ)+j = a*l₂) (hm : c*n = a*b*m+b) :
    baseArithmeticResidueWeight B m * baseArithmeticResidueWeight B l₁ *
      baseArithmeticResidueWeight B l₂ ≤
      (auxiliaryRatio B ^ (1/2 : ℝ))^3 * ∏ p ∈ G,
        residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
        residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
        residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p) := by
  apply (base_residue_three_subset_le B G hG m l₁ l₂).trans_eq
  congr 1
  apply prod_congr rfl
  intro p hp
  let : Fact p.Prime := ⟨auxiliaryPrimes_prime B p (hG hp)⟩
  have hne (x : ℕ) (hx : ¬ p ∣ x) : (x : ZMod p) ≠ 0 := by
    exact fun h => hx ((ZMod.natCast_eq_zero_iff x p).mp h)
  have hn' : (n : ZMod p) = (b : ZMod p)*(l₁ : ZMod p) := by
    simpa only [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod p)) hn
  have hj' : (n : ZMod p)+(j : ZMod p) = (a : ZMod p)*(l₂ : ZMod p) := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun x : ℤ => (x : ZMod p)) hj
  have hm' : (c : ZMod p)*(n : ZMod p) =
      (a : ZMod p)*(b : ZMod p)*(m : ZMod p)+(b : ZMod p) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using congrArg (fun x : ℕ => (x : ZMod p)) hm
  have h := graph_residue_product (a : ZMod p) b c j m l₁ l₂ n
    (hne a (ha p hp)) (hne b (hb p hp)) (hne c (hc p hp)) hn' hj' hm'
  simpa only [residueWeight, ZMod.natCast_eq_zero_iff, div_eq_mul_inv] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GraphResidueNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform normalization after discarding the coefficient primes -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graph_selected_odds_bound :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp (10*(B : ℝ)) →
      (∏ p ∈ S, (1-(1/2 : ℝ)/p)⁻¹) ≤ Real.exp 1 := by
  have ht : Tendsto (fun B : ℕ => (20/Real.log 2)*
      ((B : ℝ)/(auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have h := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (20/Real.log 2)
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using h
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hS hp)
  have hcut : ∀ p ∈ S, (auxiliaryCutoff B : ℝ) ≤ p :=
    fun p hp => (mem_filter.mp (hS hp)).2.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ 10*B/Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  apply (inverseSelectedPrimeOdds_le hP (by norm_num) (by norm_num) S hprime hcut).trans
  apply Real.exp_le_exp.mpr
  calc
    2*(S.card : ℝ)/auxiliaryCutoff B ≤ 2*(10*B/Real.log 2)/auxiliaryCutoff B :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hP.le
    _ = (20/Real.log 2)*((B : ℝ)/auxiliaryCutoff B) := by ring
    _ ≤ 1 := hsmall.le

theorem three_root_product_le_half_cube (G : Finset ℕ)
    (hG : ∀ p ∈ G, p.Prime) :
    (∏ p ∈ G, (1-3/(2*(p : ℝ)))) ≤ (primeNormalizer G (1/2))^3 := by
  unfold primeNormalizer
  rw [← prod_pow]
  apply Finset.prod_le_prod
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hG p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have h : (3 : ℝ)/(2*p) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hG p hp).two_le
    have hx : 0 ≤ (1/2 : ℝ)/p := by positivity
    have hx1 : (1/2 : ℝ)/p ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hh := mul_nonneg (sq_nonneg ((1/2 : ℝ)/p)) (show 0 ≤ 3-(1/2 : ℝ)/p by linarith)
    have he : (3 : ℝ)/(2*p) = 3*((1/2 : ℝ)/p) := by ring
    rw [he]
    nlinarith

theorem primeNormalizer_sdiff {P S : Finset ℕ} (hS : S ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) :
    primeNormalizer (P\S) (1/2) = primeNormalizer P (1/2) *
      ∏ p ∈ S, (1-(1/2 : ℝ)/p)⁻¹ := by
  have hp (p : ℕ) (hp : p ∈ S) : (1-(1/2 : ℝ)/p) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (hS hp)).two_le
    have hd : (1/2 : ℝ)/p < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  unfold primeNormalizer
  rw [← prod_sdiff hS (f := fun p : ℕ => 1-(1/2 : ℝ)/p), prod_inv_distrib]
  rw [mul_assoc, mul_inv_cancel₀ (prod_ne_zero_iff.mpr hp), mul_one]

/-- This is uniform in the later regularity cutoff. Only Mertens' cited
reciprocal-prime input is used for the normalization. -/
theorem graph_three_root_normalization
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp (10*(B : ℝ)) →
      (auxiliaryRatio B^(1/2 : ℝ))^3 *
        (∏ p ∈ auxiliaryPrimes B\S, (1-3/(2*(p : ℝ)))) ≤ K := by
  let C : ℝ := (4 : ℝ)^(-(1/2 : ℝ))+1
  have hC : 0 < C := by unfold C; positivity
  refine ⟨(C*Real.exp 1)^3, by positivity, ?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1/2) (by norm_num) (by norm_num)
  filter_upwards [graph_selected_odds_bound,
    ht.eventually (Iio_mem_nhds (show (4 : ℝ)^(-(1/2 : ℝ)) < C by dsimp [C] <;> linarith)),
    eventually_gt_atTop 1] with B hS hnorm hB
  intro S hSP hprod
  have hR := (auxiliaryRatio_pos hB).le
  have hq := (primeNormalizer_bounds (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).1
  have hsmall : primeNormalizer (auxiliaryPrimes B\S) (1/2) *
      auxiliaryRatio B^(1/2 : ℝ) ≤ C*Real.exp 1 := by
    rw [primeNormalizer_sdiff hSP (auxiliaryPrimes_prime B), mul_right_comm]
    exact mul_le_mul hnorm.le (hS S hSP hprod)
      (prod_nonneg (fun p hp => by
        have hp0 := (primeNormalizer_bounds {p} (by simpa using auxiliaryPrimes_prime B p (hSP hp))
          (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).1
        simpa only [primeNormalizer, prod_singleton] using inv_nonneg.mpr hp0)) hC.le
  calc
    _ ≤ (auxiliaryRatio B^(1/2 : ℝ))^3 *
        (primeNormalizer (auxiliaryPrimes B\S) (1/2))^3 :=
      mul_le_mul_of_nonneg_left (three_root_product_le_half_cube _
        (fun p hp => auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1)) (by positivity)
    _ = (primeNormalizer (auxiliaryPrimes B\S) (1/2)*
        auxiliaryRatio B^(1/2 : ℝ))^3 := by ring
    _ ≤ (C*Real.exp 1)^3 := pow_le_pow_left₀
      (mul_nonneg (primeNormalizer_bounds _
        (fun p hp => auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1)
        (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).1
        (Real.rpow_nonneg hR _)) hsmall 3

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEdgeMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three-root majorant for the actual arithmetic edge weights -/

namespace JointDickman
open Finset

theorem divisorEdge_residue_majorant {a b c N : ℕ} {j : ℤ}
    (B : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    baseArithmeticResidueWeight B (divisorEdgeInverse a b c n) *
      baseArithmeticResidueWeight B (n/b) *
      baseArithmeticResidueWeight B (((n : ℤ)+j).toNat/a) ≤
      graphResidueEnvelope B a b c j n := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨_,_,_,hca,hcb⟩ := mem_filter.mp hm
  obtain ⟨hqa,hqb⟩ := divisorEdge_new_quotients ha hb hc he hcop hn
  have hnb : n = b*(n/b) := (Nat.mul_div_cancel' (mem_filter.mp hn).2.1).symm
  have hend : (n : ℤ)+j = ((a*((b*divisorEdgeInverse a b c n+1)/c) : ℕ) : ℤ) := by
    have h := natural_divisor_edge_endpoints hc hca hcb he
    rwa [hback] at h
  have hcn : c*n = a*b*divisorEdgeInverse a b c n+b := by
    calc
      c*n = c*(b*((a*divisorEdgeInverse a b c n+1)/c)) :=
        congrArg (fun x : ℕ => c*x) hback.symm
      _ = b*(c*((a*divisorEdgeInverse a b c n+1)/c)) := by ring
      _ = b*(a*divisorEdgeInverse a b c n+1) := by rw [Nat.mul_div_cancel' hca]
      _ = _ := by ring
  have hend' : (n : ℤ)+j = (a : ℤ)*(((n : ℤ)+j).toNat/a : ℕ) := by
    rw [← hqb]
    exact hend
  exact graph_quotient_residue_majorant B (graphGoodPrimes B a b c)
    (filter_subset _ _) a b c _ _ _ n j
    (fun p hp => (mem_filter.mp hp).2.1)
    (fun p hp => (mem_filter.mp hp).2.2.1)
    (fun p hp => (mem_filter.mp hp).2.2.2) hnb hend' hcn

theorem arithmeticGraphPairWeight_le_base (B L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    (a b c : ℕ) (j : ℤ) (n : ℕ) :
    arithmeticGraphPairWeight B L τ C u v a b c j n ≤
      (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
        (baseArithmeticResidueWeight B (divisorEdgeInverse a b c n) *
          baseArithmeticResidueWeight B (n/b) *
          baseArithmeticResidueWeight B (((n : ℤ)+j).toNat/a)) := by
  have hfac (d l : ℕ) (w : ℝ) (hw : w ≤ 1) :
      (regularCoefficientWeight B L τ C d * arithmeticResidueWeight B L τ C l)*w ≤
        coefficientWeight B d * baseArithmeticResidueWeight B l := by
    apply (mul_le_of_le_one_right (mul_nonneg (regularCoefficientWeight_nonneg B L τ C d)
      (regularResidueWeight_nonneg B L τ C _)) hw).trans
    exact mul_le_mul (regularCoefficientWeight_le B L τ C d)
      (arithmeticResidueWeight_le_base B L τ C l)
      (regularResidueWeight_nonneg B L τ C _) (coefficientWeight_nonneg B d)
  have hC := hfac c (divisorEdgeInverse a b c n) (u c) (hu c).2
  have hA := hfac a (n/b) (v a c) (hv a c).2
  have hB := hfac b (((n : ℤ)+j).toNat/a) (v b c) (hv b c).2
  have hleft : 0 ≤ (u c * regularCoefficientWeight B L τ C c *
      arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n)) *
      (regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C (n/b) * v a c) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hu c).1 (regularCoefficientWeight_nonneg B L τ C c))
      (regularResidueWeight_nonneg B L τ C _))
      (mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg B L τ C a)
        (regularResidueWeight_nonneg B L τ C _)) (hv a c).1)
  have hA0 := mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg B L τ C a)
    (regularResidueWeight_nonneg B L τ C (coefficientPrimeSet B (n/b)))) (hv a c).1
  have hC0 := mul_nonneg (coefficientWeight_nonneg B c)
    (baseArithmeticResidueWeight_nonneg B (divisorEdgeInverse a b c n))
  have hB0 := mul_nonneg (coefficientWeight_nonneg B b)
    (baseArithmeticResidueWeight_nonneg B (((n : ℤ)+j).toNat/a))
  have hCA := mul_le_mul hC hA hA0 hC0
  have hCAB := mul_le_mul_of_nonneg_right hCA hB0
  unfold arithmeticGraphPairWeight
  calc
    _ ≤ ((regularCoefficientWeight B L τ C c *
        arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n))*u c) *
      (regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C (n/b)*v a c) *
        (coefficientWeight B b * baseArithmeticResidueWeight B (((n : ℤ)+j).toNat/a)) := by
      have hh := mul_le_mul_of_nonneg_left hB hleft
      convert hh using 1 <;> first | rfl | ring
    _ ≤ _ := by convert hCAB using 1 <;> first | rfl | ring

theorem arithmeticGraphPairWeight_residue_bound {B L a b c N : ℕ} (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    {j : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    arithmeticGraphPairWeight B L τ C u v a b c j n ≤
      (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
        graphResidueEnvelope B a b c j n :=
  (arithmeticGraphPairWeight_le_base B L τ C u v hu hv a b c j n).trans
    (mul_le_mul_of_nonneg_left (divisorEdge_residue_majorant B ha hb hc he hcop hn)
      (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B c) (coefficientWeight_nonneg B a))
        (coefficientWeight_nonneg B b)))

theorem divisorEdge_small_endpoint {a b c T N : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (he : (a : ℤ)-b = j*c)
    (hcop : a.Coprime j.natAbs) (hbT : b < 2*(T*c))
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) : n < 2*T*N := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨hmN,ham,_,hca,_⟩ := mem_filter.mp hm
  have hN : 0 < N := Nat.pos_of_ne_zero (by intro h; simp [h] at hmN)
  have hcn : c*n = b*(a*divisorEdgeInverse a b c n+1) := by
    calc
      c*n = c*(b*((a*divisorEdgeInverse a b c n+1)/c)) :=
        congrArg (fun x : ℕ => c*x) hback.symm
      _ = b*(c*((a*divisorEdgeInverse a b c n+1)/c)) := by ring
      _ = _ := by rw [Nat.mul_div_cancel' hca]
  have h1 : c*n ≤ b*N := by rw [hcn]; exact Nat.mul_le_mul_left b (by omega)
  have h2 : b*N < (2*(T*c))*N := Nat.mul_lt_mul_of_pos_right hbT hN
  have hh : c*n < c*(2*T*N) := by nlinarith [h1.trans_lt h2]
  exact Nat.lt_of_mul_lt_mul_left hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GraphResidueMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact mean of a congruence and the three-root graph majorant -/

namespace JointDickman
open Finset

theorem coprime_residue_product_mean {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d.Coprime q) (f : ZMod d → ℝ) (g : ZMod q → ℝ) :
    (∑ x : ZMod (d*q), f (x.val : ZMod d) * g (x.val : ZMod q)) /
        ((d : ℝ)*q) =
      ((∑ x : ZMod d, f x)/d) * ((∑ x : ZMod q, g x)/q) := by
  let e := ZMod.chineseRemainder hdq
  have he (x : ZMod (d*q)) : e x = ((x.val : ZMod d), (x.val : ZMod q)) := by
    have h := map_natCast e x.val
    rw [ZMod.natCast_zmod_val] at h
    exact h
  have hs := e.toEquiv.sum_comp (fun y : ZMod d × ZMod q => f y.1 * g y.2)
  change (∑ x, f (e x).1 * g (e x).2) = _ at hs
  simp only [he, Fintype.sum_prod_type, ← mul_sum, ← sum_mul] at hs
  rw [hs]
  ring

theorem prime_residue_product_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero p.val] [NeZero (∏ p ∈ P, p)]
    (f : ∀ p : P, ZMod p.val → ℝ) :
    (∑ x : ZMod (∏ p ∈ P, p), ∏ p : P, f p (x.val : ZMod p.val)) /
      (∏ p ∈ P, (p : ℝ)) = ∏ p : P, (∑ y : ZMod p.val, f p y)/(p.val : ℝ) := by
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p p.property).ne_zero⟩
  let : NeZero (∏ p ∈ P, p) := ⟨prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)⟩
  have hpq : Pairwise (fun p q : P => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have hr := residue_sum_eq_range
    (fun x : ZMod (∏ p ∈ P, p) => ((∏ p : P, f p (x.val : ZMod p.val) : ℝ) : ℂ))
  have hsum : (∑ x : ZMod (∏ p ∈ P, p), ∏ p : P, f p (x.val : ZMod p.val)) =
      ∑ n ∈ range (∏ p ∈ P, p), ∏ p : P, f p (n : ZMod p.val) := by
    have hn (n : ℕ) (hn : n ∈ range (∏ p ∈ P, p)) :
        (n : ZMod (∏ p ∈ P, p)).val = n :=
      ZMod.val_natCast_of_lt (mem_range.mp hn)
    have hr' : (∑ x : ZMod (∏ p ∈ P, p), ∏ p : P, f p (x.val : ZMod p.val)) =
      ∑ n ∈ range (∏ p ∈ P, p), ∏ p : P,
        f p ((n : ZMod (∏ p ∈ P, p)).val : ZMod p.val) := by exact_mod_cast hr
    rw [hr']
    exact sum_congr rfl (fun n hn' => by rw [hn n hn'])
  rw [hsum, ← P.prod_coe_sort (fun p : ℕ => p),
    ← P.prod_coe_sort (fun p : ℕ => (p : ℝ))]
  exact crt_product_mean (fun p : P => p.val) hpq f

open Classical in
/-- The endpoint congruence contributes its exact density; the remaining
three-root factors are independent of it by CRT. -/
theorem congruence_three_root_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {d : ℕ} [NeZero d] [NeZero (∏ p ∈ P, p)] [∀ p : P, NeZero p.val]
    (hcop : d.Coprime (∏ p ∈ P, p)) (r : ZMod d)
    (a b c : ∀ p : P, ZMod p.val)
    (hab : ∀ p, a p ≠ b p) (hac : ∀ p, a p ≠ c p) (hbc : ∀ p, b p ≠ c p) :
    (∑ x : ZMod (d * ∏ p ∈ P, p),
      (if (x.val : ZMod d) = r then (1 : ℝ) else 0) *
      ∏ p : P, residueWeight (1/2) (a p) (x.val : ZMod p.val) *
        residueWeight (1/2) (b p) (x.val : ZMod p.val) *
        residueWeight (1/2) (c p) (x.val : ZMod p.val)) /
        ((d : ℝ) * ∏ p ∈ P, (p : ℝ)) =
      (1/(d : ℝ)) * ∏ p ∈ P, (1 - 3/(2*(p : ℝ))) := by
  let q := ∏ p ∈ P, p
  let : NeZero q := ⟨prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)⟩
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p p.property).ne_zero⟩
  let f (p : P) (x : ZMod p.val) :=
    residueWeight (1/2) (a p) x * residueWeight (1/2) (b p) x *
      residueWeight (1/2) (c p) x
  have hred (x : ZMod (d*q)) (p : P) :
      (((x.val : ZMod q).val : ℕ) : ZMod p.val) = (x.val : ZMod p.val) := by
    have hd : p.val ∣ q := dvd_prod_of_mem id p.property
    rw [ZMod.val_natCast]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    exact Nat.mod_mod_of_dvd x.val hd
  have hprod (x : ZMod (d*q)) :
      (∏ p : P, f p (((x.val : ZMod q).val : ℕ) : ZMod p.val)) =
        ∏ p : P, f p (x.val : ZMod p.val) := by
    apply prod_congr rfl
    intro p _
    rw [hred]
  have h := coprime_residue_product_mean hcop
    (fun x : ZMod d => if x = r then (1 : ℝ) else 0)
    (fun x : ZMod q => ∏ p : P, f p (x.val : ZMod p.val))
  simp only [hprod, sum_ite_eq', mem_univ, ite_true, if_true] at h
  have hp := prime_residue_product_mean P hP f
  simp only [f, graph_three_root_mean _ _ _ (hab _) (hac _) (hbc _)] at hp
  simp only [f, q, Nat.cast_prod] at h
  rw [hp] at h
  rw [P.prod_coe_sort (fun p : ℕ => 1 - 3/(2*(p : ℝ)))] at h
  simpa only [f, q, Nat.cast_prod] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEndpointDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact density of the endpoint congruences and retained roots -/

namespace JointDickman
open Finset

theorem graph_endpoint_congruence {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (j : ℤ) (n : ℕ) :
    (b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j) ↔
      (n : ZMod (a*b)) = graphEndpointResidue a b j hab := by
  have hn : (ZMod.chineseRemainder hab) (n : ZMod (a*b)) =
      ((n : ZMod a), (n : ZMod b)) := map_natCast _ _
  rw [graphEndpointResidue, ← (ZMod.chineseRemainder hab).apply_eq_iff_eq]
  change _ ↔ (ZMod.chineseRemainder hab) (n : ZMod (a*b)) =
    (ZMod.chineseRemainder hab) ((ZMod.chineseRemainder hab).symm (-(j : ZMod a), 0))
  rw [(ZMod.chineseRemainder hab).apply_symm_apply, hn, Prod.mk.injEq]
  rw [ZMod.natCast_eq_zero_iff, ← add_eq_zero_iff_eq_neg]
  have he : (n : ZMod a)+(j : ZMod a) = ((n : ℤ)+j : ℤ) := by
    simp only [Int.cast_add, Int.cast_natCast]
  rw [he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact and_comm

open Classical in
/-- Exact finite-period mean; the coefficient congruences cost `1/(ab)`.
The three retained roots do not interact with this congruence. -/
theorem graph_endpoint_three_root_mean {a b c : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    [NeZero (∏ p ∈ P, p)] [∀ p : P, NeZero p.val]
    (hcop : (a*b).Coprime (∏ p ∈ P, p)) (j : ℤ)
    (ha : ∀ p ∈ P, ¬p ∣ a) (hb : ∀ p ∈ P, ¬p ∣ b) (hc : ∀ p ∈ P, ¬p ∣ c)
    (hj : ∀ p ∈ P, (j : ZMod p) ≠ 0) (he : (a : ℤ) = b+j*c) :
    (∑ x : ZMod (a*b*∏ p ∈ P, p),
      (if b ∣ x.val ∧ (a : ℤ) ∣ (x.val : ℤ)+j then (1 : ℝ) else 0) *
      ∏ p : P, residueWeight (1/2) (0 : ZMod p.val) (x.val : ZMod p.val) *
        residueWeight (1/2) (-(j : ZMod p.val)) (x.val : ZMod p.val) *
        residueWeight (1/2) ((b : ZMod p.val)*(c : ZMod p.val)⁻¹) (x.val : ZMod p.val)) /
        ((a : ℝ)*b*∏ p ∈ P, (p : ℝ)) =
      (1/((a : ℝ)*b)) * ∏ p ∈ P, (1-3/(2*(p : ℝ))) := by
  have hdist (p : P) :
      (0 : ZMod p.val) ≠ -(j : ZMod p.val) ∧
      (0 : ZMod p.val) ≠ (b : ZMod p.val)*(c : ZMod p.val)⁻¹ ∧
      -(j : ZMod p.val) ≠ (b : ZMod p.val)*(c : ZMod p.val)⁻¹ := by
    let : Fact p.val.Prime := ⟨hP p p.property⟩
    have hne (x : ℕ) (hx : ¬p.val ∣ x) : (x : ZMod p.val) ≠ 0 :=
      fun h => hx ((ZMod.natCast_eq_zero_iff x p.val).mp h)
    have he' : (a : ZMod p.val) = (b : ZMod p.val)+(j : ZMod p.val)*(c : ZMod p.val) := by
      simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul] using
        congrArg (fun x : ℤ => (x : ZMod p.val)) he
    simpa only [div_eq_mul_inv] using graph_roots_distinct (a : ZMod p.val) b c j
      (hne a (ha p p.property)) (hne b (hb p p.property)) (hne c (hc p p.property))
      (hj p p.property) he'
  have h := congruence_three_root_mean P hP hcop (graphEndpointResidue a b j hab)
    (fun p => (0 : ZMod p.val)) (fun p => -(j : ZMod p.val))
    (fun p => (b : ZMod p.val)*(c : ZMod p.val)⁻¹)
    (fun p => (hdist p).1) (fun p => (hdist p).2.1) (fun p => (hdist p).2.2)
  simp_rw [← graph_endpoint_congruence hab j] at h
  simpa only [Nat.cast_mul] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEdgePeriod
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The periodic majorant of a fixed arithmetic graph representation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem zmod_representative_reduce {d q : ℕ} [NeZero q] (hd : d ∣ q) (n : ℕ) :
    (((n : ZMod q).val : ℕ) : ZMod d) = (n : ZMod d) := by
  rw [ZMod.val_natCast]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  exact Nat.mod_mod_of_dvd n hd

theorem graphGoodPrimes_coprime (B a b c : ℕ) :
    (a*b).Coprime (∏ p ∈ graphGoodPrimes B a b c, p) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  have h := (mem_filter.mp hp).2
  have hprime := auxiliaryPrimes_prime B p (mem_filter.mp hp).1
  exact Nat.Coprime.mul_left (hprime.coprime_iff_not_dvd.mpr h.1).symm
    (hprime.coprime_iff_not_dvd.mpr h.2.1).symm

theorem graphEdgeEnvelope_natCast {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (B c : ℕ) (j : ℤ) (n : ℕ) :
    graphEdgeEnvelope B a b c j (n : ZMod (graphEdgePeriod B a b c)).val =
      graphEdgeEnvelope B a b c j n := by
  classical
  let : NeZero (graphEdgePeriod B a b c) :=
    ⟨(graphEdgePeriod_pos (NeZero.pos a) (NeZero.pos b) B c).ne'⟩
  have habd : a*b ∣ graphEdgePeriod B a b c := dvd_mul_right _ _
  have hind := zmod_representative_reduce habd n
  have hiff : (b ∣ (n : ZMod (graphEdgePeriod B a b c)).val ∧
      (a : ℤ) ∣ ((n : ZMod (graphEdgePeriod B a b c)).val : ℤ)+j) ↔
      (b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j) := by
    rw [graph_endpoint_congruence hab, graph_endpoint_congruence hab, hind]
  unfold graphEdgeEnvelope
  rw [if_congr hiff rfl rfl]
  split_ifs
  · unfold graphResidueEnvelope
    congr 1
    apply prod_congr rfl
    intro p hp
    have hpd : p ∣ graphEdgePeriod B a b c :=
      (dvd_prod_of_mem id hp).trans (dvd_mul_left _ _)
    rw [zmod_representative_reduce hpd]
  · rfl

theorem graphEdgeEnvelope_mean {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (B c : ℕ) (j : ℤ)
    (hj : ∀ p ∈ graphGoodPrimes B a b c, (j : ZMod p) ≠ 0)
    (he : (a : ℤ) = b+j*c) :
    letI : NeZero (graphEdgePeriod B a b c) :=
      ⟨(graphEdgePeriod_pos (NeZero.pos a) (NeZero.pos b) B c).ne'⟩
    (∑ x : ZMod (graphEdgePeriod B a b c), graphEdgeEnvelope B a b c j x.val) /
      (graphEdgePeriod B a b c : ℝ) = graphEdgeMean B a b c := by
  classical
  let G := graphGoodPrimes B a b c
  have hG : ∀ p ∈ G, p.Prime := fun p hp => auxiliaryPrimes_prime B p (mem_filter.mp hp).1
  let : NeZero (∏ p ∈ G, p) := ⟨prod_ne_zero_iff.mpr (fun p hp => (hG p hp).ne_zero)⟩
  let : ∀ p : G, NeZero p.val := fun p => ⟨(hG p p.property).ne_zero⟩
  have hm := graph_endpoint_three_root_mean hab G hG (graphGoodPrimes_coprime B a b c) j
    (fun p hp => (mem_filter.mp hp).2.1)
    (fun p hp => (mem_filter.mp hp).2.2.1)
    (fun p hp => (mem_filter.mp hp).2.2.2) hj he
  have hprod (n : ℕ) :
      (∏ p : G, residueWeight (1/2) (0 : ZMod p.val) (n : ZMod p.val) *
        residueWeight (1/2) (-(j : ZMod p.val)) (n : ZMod p.val) *
        residueWeight (1/2) ((b : ZMod p.val)*(c : ZMod p.val)⁻¹) (n : ZMod p.val)) =
      ∏ p ∈ G, residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
        residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
        residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p) :=
    G.prod_coe_sort (fun p : ℕ => residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
      residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
      residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p))
  simp_rw [hprod] at hm
  unfold graphEdgeEnvelope graphResidueEnvelope graphEdgePeriod graphEdgeMean
  have hid (n : ℕ) :
      (if b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j then
        (auxiliaryRatio B^(1/2 : ℝ))^3 *
          ∏ p ∈ G, residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
            residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
            residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p)
        else 0) =
      (auxiliaryRatio B^(1/2 : ℝ))^3 *
        ((if b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j then (1 : ℝ) else 0) *
          ∏ p ∈ G, residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
            residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
            residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p)) := by
    split_ifs <;> simp
  simp_rw [show graphGoodPrimes B a b c = G from rfl, hid]
  rw [← mul_sum, mul_div_assoc]
  simpa only [Nat.cast_mul, Nat.cast_prod] using congrArg
    (fun t : ℝ => (auxiliaryRatio B^(1/2 : ℝ))^3*t) hm

theorem graphEdgeEnvelope_average_tendsto {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (B c : ℕ) (j : ℤ)
    (hj : ∀ p ∈ graphGoodPrimes B a b c, (j : ZMod p) ≠ 0)
    (he : (a : ℤ) = b+j*c) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, graphEdgeEnvelope B a b c j n)/(N : ℝ))
      atTop (𝓝 (graphEdgeMean B a b c)) := by
  let : NeZero (graphEdgePeriod B a b c) :=
    ⟨(graphEdgePeriod_pos (NeZero.pos a) (NeZero.pos b) B c).ne'⟩
  have h := real_periodic_moment_tendsto
    (fun x : ZMod (graphEdgePeriod B a b c) => graphEdgeEnvelope B a b c j x.val) 1
  simpa only [pow_one, graphEdgeEnvelope_natCast hab,
    graphEdgeEnvelope_mean hab B c j hj he] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEdgeMeanBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized edge majorant is uniform in the coefficients -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graph_good_lag_ne_zero {B a b c : ℕ} {j : ℤ}
    (hj : j ≠ 0) (hsmall : j.natAbs ≤ auxiliaryCutoff B) :
    ∀ p ∈ graphGoodPrimes B a b c, (j : ZMod p) ≠ 0 := by
  intro p hp hz
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd j p).mp hz
  have hnat : p ∣ j.natAbs := Int.natCast_dvd.mp hdiv
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hj) hnat
  have hpgt : auxiliaryCutoff B < p := by
    exact_mod_cast (mem_filter.mp (mem_filter.mp hp).1).2
  omega

theorem graph_bad_primes_product_le {B a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∏ p ∈ auxiliaryPrimes B\graphGoodPrimes B a b c, p) ≤ a*b*c := by
  have hprime : ∀ p ∈ auxiliaryPrimes B\graphGoodPrimes B a b c, p.Prime :=
    fun p hp => auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1
  apply Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos ha hb) hc)
  apply (primeProduct_dvd_iff _ hprime _).mpr
  intro p hp
  have hnot := (mem_sdiff.mp hp).2
  by_cases hpa : p ∣ a
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpa b) c
  by_cases hpb : p ∣ b
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpb a) c
  by_cases hpc : p ∣ c
  · exact dvd_mul_of_dvd_right hpc (a*b)
  exact False.elim (hnot (mem_filter.mpr ⟨(mem_sdiff.mp hp).1,hpa,hpb,hpc⟩))

theorem graphEdgeMean_bound (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      (a : ℝ)*b*c ≤ Real.exp (10*(B : ℝ)) →
        graphEdgeMean B a b c ≤ K/((a : ℝ)*b) := by
  obtain ⟨K,hK,hbound⟩ := graph_three_root_normalization hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro a b c ha hb hc hsize
  let S := auxiliaryPrimes B\graphGoodPrimes B a b c
  have hS : S ⊆ auxiliaryPrimes B := sdiff_subset
  have hprod : (∏ p ∈ S, p : ℕ) ≤ Real.exp (10*(B : ℝ)) := by
    have h := graph_bad_primes_product_le (B := B) ha hb hc
    have h' : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (a : ℝ)*b*c := by exact_mod_cast h
    exact h'.trans hsize
  have hSG : auxiliaryPrimes B\S = graphGoodPrimes B a b c :=
    Finset.sdiff_sdiff_eq_self (filter_subset _ _)
  have h := hB S hS hprod
  rw [hSG] at h
  unfold graphEdgeMean
  calc
    _ = ((auxiliaryRatio B^(1/2 : ℝ))^3 *
        ∏ p ∈ graphGoodPrimes B a b c, (1-3/(2*(p : ℝ))))/((a : ℝ)*b) := by ring
    _ ≤ K/((a : ℝ)*b) := div_le_div_of_nonneg_right h (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientThreeForm
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient three-form bound with an explicit remainder -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficient_three_form_with_remainder
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z j u v w x : ℕ, 1 < B → 2 ≤ Z →
      auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z → j ≠ 0 → u ≤ v → w ≤ x →
      (∑ b ∈ Ico u v, ∑ c ∈ Ico w x,
        coefficientWeight B b * coefficientWeight B c * coefficientWeight B (b + j * c)) ≤
      C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j +
        coefficientScale B ^ 3 *
          (2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) := by
  obtain ⟨C, hC, hsieve⟩ := three_form_rectangle_sieve hFord hM
  obtain ⟨M, hM0, hnorm⟩ := coefficient_sieve_density_bound hM hδ
  refine ⟨C * M ^ 3, by positivity, ?_⟩
  intro B Z j u v w x hB hZ hPZ hlog hj huv hwx
  have hnormal := hnorm B Z hB hPZ hlog
  have hpow := pow_le_pow_left₀
    (mul_nonneg (coefficientScale_nonneg B) (roughSieveDensity_nonneg _ _)) hnormal 3
  have hP (p : ℕ) (hp : p ∈ sievePrimes Z) : p.Prime ∧ p ≤ Z ∧ 6 ≤ p := by
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hp
    obtain ⟨hpZ, hpp⟩ := Nat.mem_primesLE.mp hpZ
    exact ⟨hpp, hpZ, hp6⟩
  have hs := hsieve (sievePrimes Z) (roughSieveTheta (auxiliaryCutoff B)) j u v w x Z hj
    huv hwx hZ hP (fun p _ => roughSieveTheta_bounds _ p)
  have hprod : (∏ p ∈ sievePrimes Z, (1 - (1 - roughSieveTheta (auxiliaryCutoff B) p) / p)) =
      roughSieveDensity (auxiliaryCutoff B) Z := rfl
  rw [hprod] at hs
  have harea : 0 ≤ ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast huv))
      (sub_nonneg.mpr (by exact_mod_cast hwx)))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
  calc
    _ ≤ ∑ b ∈ Ico u v, ∑ c ∈ Ico w x,
        coefficientScale B ^ 3 *
          threeFormSieveWeight (sievePrimes Z) (roughSieveTheta (auxiliaryCutoff B)) j b c :=
      sum_le_sum (fun b _ => sum_le_sum (fun c _ => coefficient_triple_le_sieved B Z j b c))
    _ = coefficientScale B ^ 3 *
        (∑ b ∈ Ico u v, ∑ c ∈ Ico w x,
          threeFormSieveWeight (sievePrimes Z) (roughSieveTheta (auxiliaryCutoff B)) j b c) := by
      simp_rw [mul_sum]
    _ ≤ coefficientScale B ^ 3 *
        (C * ((v : ℝ) - u) * ((x : ℝ) - w) *
          roughSieveDensity (auxiliaryCutoff B) Z ^ 3 * singularFactor 24 j +
          2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hs (pow_nonneg (coefficientScale_nonneg B) _)
    _ ≤ _ := by
      rw [mul_add]
      apply add_le_add (b := C * M ^ 3 * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j) ?_ le_rfl
      calc
        _ = C * (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) ^ 3 *
            (((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j) := by ring
        _ ≤ C * M ^ 3 * (((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) harea
        _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientTripleBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform three-form coefficient estimate (manuscript equation (7)) -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Rectangles with both side lengths exponential in B have total
three-coefficient mass bounded by their area times Σ(j). The estimate
is uniform in every positive j and in the position of the rectangle. -/
theorem coefficient_three_form_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ j u v w x : ℕ,
      j ≠ 0 → u ≤ v → w ≤ x →
      Real.exp (δ * B) ≤ (v : ℝ) - u → Real.exp (δ * B) ≤ (x : ℝ) - w →
      (∑ b ∈ Ico u v, ∑ c ∈ Ico w x,
        coefficientWeight B b * coefficientWeight B c * coefficientWeight B (b + j * c)) ≤
        C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j := by
  obtain ⟨C, hC, hbound⟩ := coefficient_three_form_with_remainder hFord hM
    (by linarith : 0 < (δ / 8) / 2)
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8),
    coefficient_rectangle_remainder_small hδ, eventually_gt_atTop 1] with B hcut herror hB
  intro j u v w x hj huv hwx hL hH
  have h := hbound B (sieveCutoff (δ / 8) B) j u v w x hB hcut.1 hcut.2.1 hcut.2.2.1 hj huv hwx
  have herr := herror ((v : ℝ) - u) ((x : ℝ) - w) hL hH
  have harea : 0 ≤ ((v : ℝ) - u) * ((x : ℝ) - w) :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast huv)) (sub_nonneg.mpr (by exact_mod_cast hwx))
  calc
    _ ≤ C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j +
        ((v : ℝ) - u) * ((x : ℝ) - w) := h.trans (add_le_add le_rfl herr)
    _ ≤ C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j +
        (((v : ℝ) - u) * ((x : ℝ) - w)) * singularFactor 24 j :=
      add_le_add le_rfl (le_mul_of_one_le_right harea (singularFactor_one_le (by norm_num) j))
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphCoefficientMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the harmonic coefficient mass for a fixed positive lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphCoefficientHarmonicTerm_nonneg (B j : ℕ) (bc : ℕ × ℕ) :
    0 ≤ graphCoefficientHarmonicTerm B j bc :=
  div_nonneg (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B bc.1)
    (coefficientWeight_nonneg B bc.2)) (coefficientWeight_nonneg B (bc.1+j*bc.2)))
    (by positivity)

theorem graphCoefficientHarmonic_box
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T k j : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      k ∈ Ico B (4*B) → j ≠ 0 →
      (∑ bc ∈ coefficientDyadicBox T k, graphCoefficientHarmonicTerm B j bc) ≤
        (3*C/(T : ℝ))*singularFactor 24 j := by
  obtain ⟨C,hC,hbound⟩ := coefficient_three_form_bound hFord hM (δ := 1/2) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound, coefficientDyadicBox_scales] with B hB hscale
  intro T k j hT hTsize hk hj
  let q : ℕ := 2^k
  have hq : 0 < q := by dsimp [q] <;> positivity
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hlow : Real.exp ((1/2 : ℝ)*B) ≤ (q : ℝ) := (hscale T k hTsize hk).1
  have huv : T*q ≤ 4*T*q := by nlinarith
  have hwx : q ≤ 2*q := by omega
  have hlong₁ : Real.exp ((1/2 : ℝ)*B) ≤ (4*T*q : ℕ) - (T*q : ℝ) := by
    push_cast
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlong₂ : Real.exp ((1/2 : ℝ)*B) ≤ (2*q : ℕ) - (q : ℝ) := by
    push_cast
    linarith
  have hb := hB j (T*q) (4*T*q) q (2*q) hj huv hwx (by simpa only [Nat.cast_mul] using hlong₁) hlong₂
  have hD : (0 : ℝ) < (T*q : ℝ)^2 := sq_pos_of_pos (mul_pos hTr hqr)
  calc
    _ ≤ (∑ bc ∈ coefficientDyadicBox T k,
        coefficientWeight B bc.1 * coefficientWeight B bc.2 *
          coefficientWeight B (bc.1+j*bc.2)) / (T*q : ℝ)^2 := by
      rw [sum_div]
      apply sum_le_sum
      intro bc hbc
      have hbc' := mem_Ico.mp (mem_product.mp hbc).1
      have hlo : (T*q : ℝ) ≤ bc.1 := by exact_mod_cast hbc'.1
      have hhi : (T*q : ℝ) ≤ (bc.1+j*bc.2 : ℕ) := by
        exact_mod_cast (hbc'.1.trans (Nat.le_add_right _ _))
      have hden : (T*q : ℝ)^2 ≤ (bc.1 : ℝ)*(bc.1+j*bc.2 : ℕ) := by
        simpa only [pow_two] using mul_le_mul hlo hhi (mul_pos hTr hqr).le
          (by positivity : (0 : ℝ) ≤ bc.1)
      simp only [Nat.cast_add, Nat.cast_mul] at hden
      exact div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B bc.1)
          (coefficientWeight_nonneg B bc.2)) (coefficientWeight_nonneg B (bc.1+j*bc.2))) hD hden
    _ ≤ (C*((4*T*q : ℕ)-(T*q : ℝ))*((2*q : ℕ)-(q : ℝ))*singularFactor 24 j) /
        (T*q : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ hD.le
      simpa only [coefficientDyadicBox, q, sum_product, Nat.cast_mul, Nat.cast_ofNat] using hb
    _ = (3*C/(T : ℝ))*singularFactor 24 j := by
      push_cast
      field_simp
      ring

/-- The O(B) dyadic boxes cost only a constant per box after the harmonic
denominator is included. This is the coefficient sum in the edge mass. -/
theorem graphCoefficientHarmonic_mass
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T j : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      (∑ bc ∈ amplificationCoefficientPairs B T, graphCoefficientHarmonicTerm B j bc) ≤
        C*(B : ℝ)/(T : ℝ)*singularFactor 24 j := by
  obtain ⟨C,hC,hbox⟩ := graphCoefficientHarmonic_box hFord hM
  refine ⟨9*C, by positivity, ?_⟩
  filter_upwards [hbox] with B hB
  intro T j hT hTsize hj
  calc
    _ ≤ ∑ bc ∈ coefficientDyadicCover B T, graphCoefficientHarmonicTerm B j bc :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun bc _ _ => graphCoefficientHarmonicTerm_nonneg B j bc)
    _ = ∑ k ∈ Ico B (4*B),
        ∑ bc ∈ coefficientDyadicBox T k, graphCoefficientHarmonicTerm B j bc := by
      apply sum_biUnion
      intro k hk l hl hkl
      exact coefficientDyadicBox_disjoint T hkl
    _ ≤ ∑ _k ∈ Ico B (4*B), (3*C/(T : ℝ))*singularFactor 24 j :=
      sum_le_sum (fun k hk => hB T k j hT hTsize hk hj)
    _ = (9*C)*(B : ℝ)/(T : ℝ)*singularFactor 24 j := by
      have hcard : (Ico B (4*B)).card = 3*B := by simp; omega
      rw [sum_const, hcard, nsmul_eq_mul]
      push_cast
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphPairMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A periodic upper bound for each actual graph representation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphResidueEnvelope_nonneg (B a b c : ℕ) (j : ℤ) (n : ℕ) :
    0 ≤ graphResidueEnvelope B a b c j n := by
  unfold graphResidueEnvelope
  apply mul_nonneg
  · have hR : 0 ≤ auxiliaryRatio B := by unfold auxiliaryRatio; positivity
    exact pow_nonneg (Real.rpow_nonneg hR _) _
  · exact prod_nonneg (fun p _ => mul_nonneg
      (mul_nonneg (residueWeight_nonneg _ _ (by norm_num))
        (residueWeight_nonneg _ _ (by norm_num))) (residueWeight_nonneg _ _ (by norm_num)))

theorem graphEdgeEnvelope_nonneg (B a b c : ℕ) (j : ℤ) (n : ℕ) :
    0 ≤ graphEdgeEnvelope B a b c j n := by
  classical
  unfold graphEdgeEnvelope
  split_ifs
  · exact graphResidueEnvelope_nonneg B a b c j n
  · rfl

theorem graphPair_mass_le_prefix {B L T a b c : ℕ} (τ C : ℝ)
    (u : ℕ → ℝ) (hu : ∀ d, u d ∈ Set.Icc (0 : ℝ) 1)
    {j : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs) (N : ℕ) :
    (∑ n ∈ divisorEdgeNew a b c N j,
      arithmeticGraphPairWeight B L τ C u (amplificationInnerWeight T) a b c j n) ≤
    (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
      ∑ n ∈ range (2*T*N), graphEdgeEnvelope B a b c j n := by
  classical
  let w := arithmeticGraphPairWeight B L τ C u (amplificationInnerWeight T) a b c j
  let E := divisorEdgeNew a b c N j
  have hsupport (n : ℕ) (hn : n ∈ E) (hw : w n ≠ 0) : n < 2*T*N := by
    have hv : amplificationInnerWeight T b c ≠ 0 := by
      intro hv
      apply hw
      simp only [w, arithmeticGraphPairWeight, hv, mul_zero]
    exact divisorEdge_small_endpoint ha hc he hcop (amplificationInnerWeight_support hv).2 hn
  have hfilter : (∑ n ∈ E, w n) = ∑ n ∈ E.filter (fun n => n < 2*T*N), w n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (hsupport n hn hne)
  rw [show (∑ n ∈ divisorEdgeNew a b c N j,
      arithmeticGraphPairWeight B L τ C u (amplificationInnerWeight T) a b c j n) =
      ∑ n ∈ E.filter (fun n => n < 2*T*N), w n from hfilter]
  rw [mul_sum]
  apply (sum_le_sum (fun n hn => ?_)).trans
    (sum_le_sum_of_subset_of_nonneg (fun n hn => mem_range.mpr (mem_filter.mp hn).2)
      (fun n _ _ => mul_nonneg (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B c)
        (coefficientWeight_nonneg B a)) (coefficientWeight_nonneg B b))
        (graphEdgeEnvelope_nonneg B a b c j n)))
  have hn' := (mem_filter.mp hn).1
  have hbnd := arithmeticGraphPairWeight_residue_bound (B := B) (L := L) τ C u (amplificationInnerWeight T)
    hu (fun _ _ => amplificationBump_bounds _) ha hb hc he hcop hn'
  have hcong := (mem_filter.mp hn').2
  have hcong' : b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j := ⟨hcong.1,hcong.2.1⟩
  simpa only [w, graphEdgeEnvelope, ite_eq_left hcong'] using hbnd

theorem mean_scaled_multiple {f : ℕ → ℝ} {μ : ℝ}
    (h : Tendsto (fun N => (∑ n ∈ range N, f n)/(N : ℝ)) atTop (𝓝 μ))
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N => (∑ n ∈ range (k*N), f n)/(N : ℝ)) atTop (𝓝 ((k : ℝ)*μ)) := by
  have htop : Tendsto (fun N : ℕ => k*N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hk) tendsto_id
  have ht := (h.comp htop).const_mul (k : ℝ)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  dsimp only [Function.comp_def]
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

theorem graphPair_majorant_tendsto {a b T : ℕ} [NeZero a] [NeZero b]
    (hT : 0 < T) (hab : a.Coprime b) (B c : ℕ) (j : ℤ)
    (hj : ∀ p ∈ graphGoodPrimes B a b c, (j : ZMod p) ≠ 0)
    (he : (a : ℤ) = b+j*c) :
    Tendsto (fun N : ℕ =>
      (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
        (∑ n ∈ range (2*T*N), graphEdgeEnvelope B a b c j n)/(N : ℝ))
      atTop (𝓝 ((coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
        (2*(T : ℝ))*graphEdgeMean B a b c)) := by
  have h := (mean_scaled_multiple (graphEdgeEnvelope_average_tendsto hab B c j hj he)
    (Nat.mul_pos (by norm_num : 0 < 2) hT)).const_mul
      (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_assoc] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphCoefficientReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph coefficient triples have no multiplicity at a fixed lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTriple_subsets {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    i.1 ⊆ auxiliaryPrimes B ∧ i.2.1 ⊆ auxiliaryPrimes B ∧ i.2.2 ⊆ auxiliaryPrimes B := by
  classical
  have h := mem_product.mp (mem_filter.mp hi).1
  exact ⟨mem_powerset.mp h.1, mem_powerset.mp (mem_product.mp h.2).1,
    mem_powerset.mp (mem_product.mp h.2).2⟩

theorem graphTriple_positive_relation {B T j : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ supportedGraphTriples B T (j : ℤ)) :
    (∏ p ∈ i.2.1, p) = (∏ p ∈ i.2.2, p)+j*(∏ p ∈ i.1, p) := by
  classical
  have h := (mem_filter.mp (mem_filter.mp hi).1).2.2.2.2.1
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at h
  rw [(mem_filter.mp hi).2.1] at h
  have h' : ((∏ p ∈ i.2.1, p : ℕ) : ℤ) =
      (∏ p ∈ i.2.2, p : ℕ)+(j : ℤ)*(∏ p ∈ i.1, p : ℕ) := by linarith
  exact_mod_cast h'

theorem graphTriplePair_injective {B T : ℕ} (j : ℤ) :
    Set.InjOn graphTriplePair (supportedGraphTriples B T j : Set GraphCoefficientTriple) := by
  classical
  intro i hi k hk hik
  have hi' := (mem_filter.mp hi).1
  have hk' := (mem_filter.mp hk).1
  have his := graphTriple_subsets hi'
  have hks := graphTriple_subsets hk'
  have hD : (∏ p ∈ i.1, p) = ∏ p ∈ k.1, p := congrArg Prod.snd hik
  have hE : (∏ p ∈ i.2.2, p) = ∏ p ∈ k.2.2, p := congrArg Prod.fst hik
  have hei := (mem_filter.mp hi').2.2.2.2.1
  have hek := (mem_filter.mp hk').2.2.2.2.1
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at hei
  change ((∏ p ∈ k.2.1, p : ℕ) : ℤ)-(∏ p ∈ k.2.2, p : ℕ) =
    graphTripleLag k*(∏ p ∈ k.1, p : ℕ) at hek
  rw [(mem_filter.mp hi).2.1, hD, hE] at hei
  rw [(mem_filter.mp hk).2.1] at hek
  have hA : (∏ p ∈ i.2.1, p) = ∏ p ∈ k.2.1, p := by
    have h : ((∏ p ∈ i.2.1, p : ℕ) : ℤ) = (∏ p ∈ k.2.1, p : ℕ) := by linarith
    exact_mod_cast h
  apply Prod.ext
  · exact primeProduct_injective (auxiliaryPrimes_prime B) his.1 hks.1 hD
  · exact Prod.ext (primeProduct_injective (auxiliaryPrimes_prime B) his.2.1 hks.2.1 hA)
      (primeProduct_injective (auxiliaryPrimes_prime B) his.2.2 hks.2.2 hE)

theorem graphTriple_harmonic_le {B T j : ℕ} :
    (∑ i ∈ supportedGraphTriples B T (j : ℤ),
      (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
        coefficientWeight B (∏ p ∈ i.2.2, p)) /
          (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) ≤
      ∑ bc ∈ amplificationCoefficientPairs B T, graphCoefficientHarmonicTerm B j bc := by
  classical
  have hinj := graphTriplePair_injective (B := B) (T := T) (j : ℤ)
  have hsub : (supportedGraphTriples B T (j : ℤ)).image graphTriplePair ⊆
      amplificationCoefficientPairs B T := by
    intro bc hbc
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hbc
    exact (mem_filter.mp hi).2.2.2
  calc
    _ = ∑ i ∈ supportedGraphTriples B T (j : ℤ),
        graphCoefficientHarmonicTerm B j (graphTriplePair i) := by
      apply sum_congr rfl
      intro i hi
      rw [graphTriple_positive_relation hi]
      unfold graphCoefficientHarmonicTerm graphTriplePair
      push_cast
      ring
    _ = ∑ bc ∈ (supportedGraphTriples B T (j : ℤ)).image graphTriplePair,
        graphCoefficientHarmonicTerm B j bc := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
      (fun bc _ _ => graphCoefficientHarmonicTerm_nonneg B j bc)

theorem graphTriple_harmonic_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T j : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      (∑ i ∈ supportedGraphTriples B T (j : ℤ),
        (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
          coefficientWeight B (∏ p ∈ i.2.2, p)) /
            (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) ≤
        C*(B : ℝ)/(T : ℝ)*singularFactor 24 j := by
  obtain ⟨C,hC,hbound⟩ := graphCoefficientHarmonic_mass hFord hM
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with B hB
  intro T j hT hTs hj
  exact graphTriple_harmonic_le.trans (hB T j hT hTs hj)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphTripleSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only supported coprime coefficient triples contribute to a lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTripleWeight_nonzero_supported {B L T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (τ C : ℝ) {i : GraphCoefficientTriple} {j : ℤ}
    (hi : i ∈ arithmeticGraphTriples B T) (hlag : graphTripleLag i = j)
    {n : ℕ} (hw : graphTripleWeight B L τ C T i n ≠ 0) :
    i ∈ supportedGraphTriples B T j := by
  classical
  let a := ∏ p ∈ i.2.1, p
  let b := ∏ p ∈ i.2.2, p
  let c := ∏ p ∈ i.1, p
  have hzero (hu : amplificationOuterWeight B c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change (amplificationOuterWeight B c * _ * _) * _ * _ = 0
    rw [hu, zero_mul, zero_mul, zero_mul, zero_mul]
  have hza (hu : amplificationInnerWeight T a c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change _ * (_ * _ * amplificationInnerWeight T a c) * _ = 0
    rw [hu, mul_zero, mul_zero, zero_mul]
  have hzb (hu : amplificationInnerWeight T b c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change _ * (_ * _ * amplificationInnerWeight T b c) = 0
    rw [hu, mul_zero, mul_zero]
  have hpa : (a,c) ∈ amplificationCoefficientPairs B T := by
    by_contra hn
    have hs := amplificationSmoothWeight_support hB hT a c hn
    exact (mul_ne_zero hzero hza) hs
  have hpb : (b,c) ∈ amplificationCoefficientPairs B T := by
    by_contra hn
    have hs := amplificationSmoothWeight_support hB hT b c hn
    exact (mul_ne_zero hzero hzb) hs
  exact mem_filter.mpr ⟨hi,hlag,hpa,hpb⟩

theorem graphTriple_edge_coprime {B T N : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) {n : ℕ} (hn : n ∈ graphTripleEdges N i) :
    (∏ p ∈ i.2.1, p).Coprime (∏ p ∈ i.1, p) := by
  classical
  have hs := graphTriple_subsets hi
  have ha : 0 < ∏ p ∈ i.2.1, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.1 hp)).pos)
  have hc : 0 < ∏ p ∈ i.1, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).pos)
  have hg := (mem_filter.mp hi).2
  have hm := (divisorEdge_inverse_mem ha hc hg.2.2.2.1 hg.2.2.2.2 hn).1
  exact (coprime_of_divisor_linear_succ (mem_filter.mp hm).2.2.2.1).1

theorem graphTriple_size_bound :
    ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, 0 < T →
      (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → ∀ j : ℤ,
      ∀ i ∈ supportedGraphTriples B T j,
        ((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ)*(∏ p ∈ i.1, p : ℕ) ≤
          Real.exp (10*(B : ℝ)) := by
  filter_upwards [amplificationCoefficientPairs_size] with B hB
  intro T hT hTs j i hi
  have h := (mem_filter.mp hi).2
  have ha := hB T _ _ hT hTs h.2.1
  have hb := hB T _ _ hT hTs h.2.2
  calc
    _ ≤ Real.exp ((16/5 : ℝ)*B)*Real.exp ((16/5 : ℝ)*B)*Real.exp ((16/5 : ℝ)*B) := by
      gcongr
      exacts [ha.1, hb.1, ha.2]
    _ = Real.exp ((48/5 : ℝ)*B) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (10*(B : ℝ)) := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) B])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphLagMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual lag mass is dominated by a finite sum of periodic means -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmeticLagMass_supported {B L T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (τ C : ℝ) (N : ℕ) (j : ℤ) :
    arithmeticLagMass B L τ C T N j =
      (∑ i ∈ coprimeGraphTriples B T j, ∑ n ∈ graphTripleEdges N i,
        graphTripleWeight B L τ C T i n)/(N : ℝ) := by
  classical
  unfold arithmeticLagMass
  congr 1
  have hsub : coprimeGraphTriples B T j ⊆ arithmeticGraphTriples B T :=
    (filter_subset _ _).trans (filter_subset _ _)
  calc
    _ = ∑ i ∈ coprimeGraphTriples B T j, if graphTripleLag i = j then
        ∑ n ∈ graphTripleEdges N i, graphTripleWeight B L τ C T i n else 0 := by
      symm
      apply sum_subset hsub
      intro i hi hni
      by_cases hj : graphTripleLag i = j
      · rw [ite_eq_left hj]
        apply sum_eq_zero
        intro n hn
        by_contra hw
        exact hni (mem_filter.mpr ⟨graphTripleWeight_nonzero_supported hB hT τ C hi hj hw,
          graphTriple_edge_coprime hi hn⟩)
      · exact ite_eq_right hj
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      exact ite_eq_left (mem_filter.mp (mem_filter.mp hi).1).2.1

theorem arithmeticLagMass_le_majorant {B L T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (τ C : ℝ) (N : ℕ) (j : ℤ) :
    arithmeticLagMass B L τ C T N j ≤ graphLagMajorant B T N j := by
  classical
  rw [arithmeticLagMass_supported hB hT]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply sum_le_sum
  intro i hi
  have hi' := (mem_filter.mp (mem_filter.mp hi).1).1
  have hlag := (mem_filter.mp (mem_filter.mp hi).1).2.1
  have hs := graphTriple_subsets hi'
  have hp (D : Finset ℕ) (hD : D ⊆ auxiliaryPrimes B) : 0 < ∏ p ∈ D, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).pos)
  have hg := (mem_filter.mp hi').2
  have he := hg.2.2.2.1
  have hcop := hg.2.2.2.2
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
  change (∏ p ∈ i.2.1, p).Coprime (graphTripleLag i).natAbs at hcop
  rw [hlag] at he hcop
  have h := graphPair_mass_le_prefix (B := B) (L := L) (T := T) τ C
    (amplificationOuterWeight B) (fun _ => amplificationBump_bounds _)
    (hp _ hs.2.1) (hp _ hs.2.2) (hp _ hs.1) he hcop N
  simpa only [graphTripleWeight, graphTripleEdges, hlag] using h

theorem graphLagMajorant_tendsto {B T : ℕ} (hT : 0 < T) {j : ℤ}
    (hj : j ≠ 0) (hsmall : j.natAbs ≤ auxiliaryCutoff B) :
    Tendsto (fun N => graphLagMajorant B T N j) atTop (𝓝 (graphLagMean B T j)) := by
  classical
  simp only [graphLagMajorant, sum_div, graphLagMean]
  apply tendsto_finsetSum
  intro i hi
  have hi' := (mem_filter.mp (mem_filter.mp hi).1).1
  have hlag := (mem_filter.mp (mem_filter.mp hi).1).2.1
  have hs := graphTriple_subsets hi'
  have hp (D : Finset ℕ) (hD : D ⊆ auxiliaryPrimes B) : 0 < ∏ p ∈ D, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).pos)
  let : NeZero (∏ p ∈ i.2.1, p) := ⟨(hp _ hs.2.1).ne'⟩
  let : NeZero (∏ p ∈ i.2.2, p) := ⟨(hp _ hs.2.2).ne'⟩
  have hg := (mem_filter.mp hi').2
  have he := hg.2.2.2.1
  have hcop := hg.2.2.2.2
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
  change (∏ p ∈ i.2.1, p).Coprime (graphTripleLag i).natAbs at hcop
  rw [hlag] at he hcop
  have hab := divisor_edge_coprime (mem_filter.mp hi).2 hcop he
  have he' : ((∏ p ∈ i.2.1, p : ℕ) : ℤ) =
      (∏ p ∈ i.2.2, p : ℕ)+j*(∏ p ∈ i.1, p : ℕ) := by linarith
  exact graphPair_majorant_tendsto hT hab B _ j (graph_good_lag_ne_zero hj hsmall) he'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphLagSwap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing a coefficient representation reverses its lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTripleSwap_involutive : Function.Involutive graphTripleSwap := fun _ => rfl

theorem divisor_lag_coprime_swap {a b c : ℕ} {j : ℤ}
    (he : (a : ℤ)-b = j*c) (ha : a.Coprime j.natAbs) : b.Coprime j.natAbs := by
  apply Nat.coprime_of_dvd'
  intro p _ hpb hpj
  have hpj' : (p : ℤ) ∣ j := Int.natCast_dvd.mpr hpj
  have hpb' : (p : ℤ) ∣ (b : ℤ) := by exact_mod_cast hpb
  have hd := dvd_add hpb' (dvd_mul_of_dvd_left hpj' (c : ℤ))
  have hpa' : (p : ℤ) ∣ (a : ℤ) := by
    have hae : (a : ℤ) = b+j*c := by linarith
    rwa [← hae] at hd
  have hpa : p ∣ a := by exact_mod_cast hpa'
  exact Nat.dvd_one.mpr (Nat.eq_one_of_dvd_coprimes ha hpa hpj)

theorem graphTripleSwap_lag {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    graphTripleLag (graphTripleSwap i) = -graphTripleLag i := by
  classical
  have hs := graphTriple_subsets hi
  have hc : (∏ p ∈ i.1, p : ℕ) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).ne_zero)
  have he := (mem_filter.mp hi).2.2.2.2.1
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
  have hflip : ((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ) =
      (-graphTripleLag i)*(∏ p ∈ i.1, p : ℕ) := by linarith
  change (((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ)) /
      (∏ p ∈ i.1, p : ℕ) = -graphTripleLag i
  rw [hflip, Int.mul_ediv_cancel _ (by exact_mod_cast hc)]

theorem graphTripleSwap_mem {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) : graphTripleSwap i ∈ arithmeticGraphTriples B T := by
  classical
  have hs := graphTriple_subsets hi
  have hg := (mem_filter.mp hi).2
  have hlag := graphTripleSwap_lag hi
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_powerset.mpr hs.1,
    mem_product.mpr ⟨mem_powerset.mpr hs.2.2,mem_powerset.mpr hs.2.1⟩⟩,?_⟩
  change i.2.2 ≠ i.2.1 ∧ graphTripleLag (graphTripleSwap i) ≠ 0 ∧
    (graphTripleLag (graphTripleSwap i)).natAbs < T ∧
    ((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ) =
      graphTripleLag (graphTripleSwap i)*(∏ p ∈ i.1, p : ℕ) ∧
    (∏ p ∈ i.2.2, p).Coprime (graphTripleLag (graphTripleSwap i)).natAbs
  rw [hlag, Int.natAbs_neg, neg_ne_zero]
  refine ⟨Ne.symm hg.1,hg.2.1,hg.2.2.1,?_,?_⟩
  · have he := hg.2.2.2.1
    change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
      graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
    linarith
  · exact divisor_lag_coprime_swap hg.2.2.2.1 hg.2.2.2.2

theorem graphTripleSwap_supported {B T : ℕ} {i : GraphCoefficientTriple} {j : ℤ}
    (hi : i ∈ supportedGraphTriples B T j) :
    graphTripleSwap i ∈ supportedGraphTriples B T (-j) := by
  classical
  have h := mem_filter.mp hi
  apply mem_filter.mpr
  refine ⟨graphTripleSwap_mem h.1,?_,h.2.2.2,h.2.2.1⟩
  rw [graphTripleSwap_lag h.1,h.2.1]

theorem graphTriple_harmonic_neg (B T : ℕ) (j : ℤ) :
    (∑ i ∈ supportedGraphTriples B T (-j),
      (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
        coefficientWeight B (∏ p ∈ i.2.2, p)) /
          (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) =
    (∑ i ∈ supportedGraphTriples B T j,
      (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
        coefficientWeight B (∏ p ∈ i.2.2, p)) /
          (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) := by
  classical
  apply sum_bij (fun i _ => graphTripleSwap i)
  · intro i hi
    simpa only [neg_neg] using graphTripleSwap_supported hi
  · intro i _ k _ hik
    exact graphTripleSwap_involutive.injective hik
  · intro i hi
    exact ⟨graphTripleSwap i,graphTripleSwap_supported hi,graphTripleSwap_involutive i⟩
  · intro i _
    simp only [graphTripleSwap]
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SignedLagMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both signs of the actual lag-mass bound -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTriple_harmonic_signed_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, ∀ j : ℤ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      (∑ i ∈ supportedGraphTriples B T j,
        (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
          coefficientWeight B (∏ p ∈ i.2.2, p)) /
            (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) ≤
        C*(B : ℝ)/(T : ℝ)*singularFactor 24 j.natAbs := by
  obtain ⟨C,hC,hbound⟩ := graphTriple_harmonic_bound hFord hM
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with B hB
  intro T j hT hTs hj
  have h := hB T j.natAbs hT hTs (Int.natAbs_ne_zero.mpr hj)
  by_cases hj0 : 0 ≤ j
  · have he : (j.natAbs : ℤ) = j := by rw [Int.natCast_natAbs, abs_of_nonneg hj0]
    simpa only [he] using h
  · have he : -(j.natAbs : ℤ) = j := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hj0), neg_neg]
    simpa only [he] using (graphTriple_harmonic_neg B T (j.natAbs : ℤ)).trans_le h

theorem graphLagMean_signed_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, ∀ j : ℤ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      graphLagMean B T j ≤ K*(B : ℝ)*singularFactor 24 j.natAbs := by
  obtain ⟨K₁,hK₁,hmean⟩ := graphEdgeMean_bound hM
  obtain ⟨K₂,hK₂,hcoeff⟩ := graphTriple_harmonic_signed_bound hFord hM
  refine ⟨2*K₁*K₂, by positivity, ?_⟩
  filter_upwards [hmean,hcoeff,graphTriple_size_bound] with B hB hC hsize
  intro T j hT hTs hj
  let w (i : GraphCoefficientTriple) :=
    (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
      coefficientWeight B (∏ p ∈ i.2.2, p)) /
        (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))
  have hw (i : GraphCoefficientTriple) : 0 ≤ w i := by
    dsimp [w]
    exact div_nonneg (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B _)
      (coefficientWeight_nonneg B _)) (coefficientWeight_nonneg B _)) (by positivity)
  have hsum : (∑ i ∈ coprimeGraphTriples B T j, w i) ≤
      K₂*(B : ℝ)/(T : ℝ)*singularFactor 24 j.natAbs := by
    apply (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hw i)).trans
    exact hC T j hT hTs hj
  calc
    _ ≤ ∑ i ∈ coprimeGraphTriples B T j, (2*(T : ℝ)*K₁)*w i := by
      apply sum_le_sum
      intro i hi
      have his := (mem_filter.mp hi).1
      have hs := graphTriple_subsets (mem_filter.mp his).1
      have hp (D : Finset ℕ) (hD : D ⊆ auxiliaryPrimes B) : 0 < ∏ p ∈ D, p :=
        prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).pos)
      have he := hB _ _ _ (hp _ hs.2.1) (hp _ hs.2.2) (hp _ hs.1)
        (hsize T hT hTs j i his)
      have hmul := mul_le_mul_of_nonneg_left he
        (show 0 ≤ (coefficientWeight B (∏ p ∈ i.1, p) *
          coefficientWeight B (∏ p ∈ i.2.1, p) * coefficientWeight B (∏ p ∈ i.2.2, p)) *
            (2*(T : ℝ)) from mul_nonneg
              (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B _)
                (coefficientWeight_nonneg B _)) (coefficientWeight_nonneg B _)) (by positivity))
      convert hmul using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [w] <;> ring)
    _ = (2*(T : ℝ)*K₁) * ∑ i ∈ coprimeGraphTriples B T j, w i := (mul_sum _ _ _).symm
    _ ≤ (2*(T : ℝ)*K₁) * (K₂*(B : ℝ)/(T : ℝ)*singularFactor 24 j.natAbs) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2*K₁*K₂)*(B : ℝ)*singularFactor 24 j.natAbs := by
      have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      field_simp

/-- All regularity parameters are bounded simultaneously. They enter
only the nonnegative weights already dominated by the same majorant. -/
theorem arithmeticLagMass_signed_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, ∀ j : ℤ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      j.natAbs ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ,
        arithmeticLagMass B L τ C T N j ≤
          K*(B : ℝ)*singularFactor 24 j.natAbs+ε := by
  obtain ⟨K,hK,hmean⟩ := graphLagMean_signed_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hmean,eventually_gt_atTop 0] with B hB hB0
  intro T j hT hTs hj hjB ε hε
  have ht := graphLagMajorant_tendsto (B := B) hT
    hj hjB
  have hb := hB T j hT hTs hj
  filter_upwards [ht.eventually (Iio_mem_nhds (show graphLagMean B T j <
    K*(B : ℝ)*singularFactor 24 j.natAbs+ε by linarith))] with N hN
  intro L τ C
  exact (arithmeticLagMass_le_majorant hB0 hT τ C N j).trans hN.le


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticKernelMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual lag kernel inherits the uniform arithmetic mass bound -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmeticLagMass_eq_kernel (B L : ℕ) (τ C : ℝ) (T N : ℕ) (j : ℤ) :
    arithmeticLagMass B L τ C T N j =
      (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
        rawArithmeticGraphKernel B L τ C T N j n)/(N : ℝ) := by
  classical
  unfold arithmeticLagMass rawArithmeticGraphKernel
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  by_cases hj : graphTripleLag i = j
  · simp only [hj, true_and, ite_true, if_true]
    rw [← sum_filter]
    have hfilter : (Icc 1 (arithmeticGraphVertexCap B N)).filter
        (fun n => n ∈ graphTripleEdges N i) = graphTripleEdges N i := by
      ext n
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hn => graphTriple_edges_subset hi hn)
    rw [hfilter]
  · simp only [hj, false_and, ite_false, if_false, sum_const_zero]

/-- The normalized kernel has the manuscript's summable lag majorant.
The statement is simultaneous in every regularity parameter. -/
theorem arithmeticKernelMass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, ∀ j : ℤ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      j.natAbs ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ,
        (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
          rawArithmeticGraphKernel B L τ C T N j n)/((B : ℝ)*T*N) ≤
          K*singularFactor 24 j.natAbs/(T : ℝ)+ε := by
  obtain ⟨K,hK,hbound⟩ := arithmeticLagMass_signed_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop 0] with B hB hB0
  intro T j hT hTs hj hjB ε hε
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB0
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  filter_upwards [hB T j hT hTs hj hjB (ε*((B : ℝ)*T)) (by positivity)] with N hN
  intro L τ C
  have h := hN L τ C
  rw [arithmeticLagMass_eq_kernel] at h
  have hh := div_le_div_of_nonneg_right h (mul_pos hBr hTr).le
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  · ring
  · field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticLagCorrelations
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite sets of actual lag correlations are controlled by their mass -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem kernelLagCorrelation_abs (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (j : ℤ) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 2) :
    |kernelLagCorrelation B L τ C T N j F| ≤ 4*arithmeticKernelMass B L τ C T N j := by
  have hpair (n : ℕ) : |(star (F n)*F ((n : ℤ)+j).toNat).re| ≤ 4 := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul, norm_star]
    have h := mul_le_mul (hF n) (hF ((n : ℤ)+j).toNat) (norm_nonneg _) (by norm_num)
    norm_num at h
    exact h
  have hs : |∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
      rawArithmeticGraphKernel B L τ C T N j n * (star (F n)*F ((n : ℤ)+j).toNat).re| ≤
      4*∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N), rawArithmeticGraphKernel B L τ C T N j n := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    rw [abs_mul, abs_of_nonneg (rawArithmeticGraphKernel_nonneg B L τ C T N j n)]
    exact (mul_le_mul_of_nonneg_left (hpair n)
      (rawArithmeticGraphKernel_nonneg B L τ C T N j n)).trans_eq (mul_comm _ _)
  unfold kernelLagCorrelation arithmeticKernelMass
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (B : ℝ)*T*N)]
  convert div_le_div_of_nonneg_right hs (by positivity : 0 ≤ (B : ℝ)*T*N) using 1 <;> first | rfl | ring

theorem finite_kernelLagCorrelation_absolute_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ J : Finset ℤ, (∀ j ∈ J, j ≠ 0 ∧ j.natAbs ≤ auxiliaryCutoff B) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 2) →
        (∑ j ∈ J, |kernelLagCorrelation B L τ C T N j F|) ≤
          (4*K/(T : ℝ))*(∑ j ∈ J, singularFactor 24 j.natAbs)+ε := by
  classical
  obtain ⟨K,hK,hbound⟩ := arithmeticKernelMass_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs J hJ ε hε
  let δ : ℝ := ε/(4*((J.card : ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  have hall : ∀ᶠ N : ℕ in atTop, ∀ j ∈ J, ∀ L : ℕ, ∀ τ C : ℝ,
      arithmeticKernelMass B L τ C T N j ≤ K*singularFactor 24 j.natAbs/(T : ℝ)+δ := by
    apply (eventually_all_finset J).mpr
    intro j hj
    exact hB T j hT hTs (hJ j hj).1 (hJ j hj).2 δ hδ
  filter_upwards [hall] with N hN
  intro L τ C F hF
  have herr : 4*(J.card : ℝ)*δ ≤ ε := by
    have hc : (J.card : ℝ) ≤ (J.card : ℝ)+1 := by linarith
    calc
      _ ≤ 4*((J.card : ℝ)+1)*δ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (by norm_num)) hδ.le
      _ = ε := by dsimp [δ]; field_simp
  calc
    _ ≤ ∑ j ∈ J, 4*(K*singularFactor 24 j.natAbs/(T : ℝ)+δ) := by
      apply sum_le_sum
      intro j hj
      exact (kernelLagCorrelation_abs B L τ C T N j F hF).trans
        (mul_le_mul_of_nonneg_left (hN j hj L τ C) (by norm_num))
    _ = (4*K/(T : ℝ))*(∑ j ∈ J, singularFactor 24 j.natAbs)+4*(J.card : ℝ)*δ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul]
      rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro j _
        ring
      · ring
    _ ≤ _ := by linarith only [herr]

theorem finite_kernelLagCorrelation_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ J : Finset ℤ, (∀ j ∈ J, j ≠ 0 ∧ j.natAbs ≤ auxiliaryCutoff B) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 2) →
        |∑ j ∈ J, kernelLagCorrelation B L τ C T N j F| ≤
          (4*K/(T : ℝ))*(∑ j ∈ J, singularFactor 24 j.natAbs)+ε := by
  obtain ⟨K,hK,hbound⟩ := finite_kernelLagCorrelation_absolute_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs J hJ ε hε
  filter_upwards [hB T hT hTs J hJ ε hε] with N hN
  intro L τ C F hF
  exact (abs_sum_le_sum_abs _ _).trans (hN L τ C F hF)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortLagSet
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The singular factor has bounded mean on both signs of the short lags -/

namespace JointDickman
open Finset

theorem mem_nonzeroShortLags {H : ℕ} {j : ℤ} :
    j ∈ nonzeroShortLags H ↔ j ≠ 0 ∧ j.natAbs ≤ H := by
  simp only [nonzeroShortLags, mem_erase, mem_Icc]
  constructor
  · rintro ⟨hj,hl,hu⟩
    refine ⟨hj,?_⟩
    have h : |j| ≤ (H : ℤ) := abs_le.mpr ⟨hl,hu⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · rintro ⟨hj,h⟩
    have h' : |j| ≤ (H : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast h
    exact ⟨hj,(abs_le.mp h').1,(abs_le.mp h').2⟩

theorem nonzeroShortLags_eq (H : ℕ) :
    nonzeroShortLags H = (Ioc 0 H).image (fun n : ℕ => (n : ℤ)) ∪
      (Ioc 0 H).image (fun n : ℕ => -(n : ℤ)) := by
  ext j
  rw [mem_nonzeroShortLags, mem_union]
  constructor
  · rintro ⟨hj,hjH⟩
    have hn : j.natAbs ∈ Ioc 0 H := mem_Ioc.mpr ⟨Int.natAbs_pos.mpr hj,hjH⟩
    by_cases h : 0 ≤ j
    · exact Or.inl (mem_image.mpr ⟨j.natAbs,hn,by rw [Int.natCast_natAbs,abs_of_nonneg h]⟩)
    · exact Or.inr (mem_image.mpr ⟨j.natAbs,hn,by
        rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge h),neg_neg]⟩)
  · intro hj
    rcases hj with hj | hj
    · obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
      simp only [Int.natAbs_natCast]
      exact ⟨by exact_mod_cast (mem_Ioc.mp hn).1.ne', (mem_Ioc.mp hn).2⟩
    · obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
      simp only [Int.natAbs_neg,Int.natAbs_natCast,neg_ne_zero]
      exact ⟨by exact_mod_cast (mem_Ioc.mp hn).1.ne', (mem_Ioc.mp hn).2⟩

theorem sum_shortLag_natAbs (H : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ nonzeroShortLags H, f j.natAbs) = 2*∑ n ∈ Ioc 0 H, f n := by
  classical
  have hd : Disjoint ((Ioc 0 H).image (fun n : ℕ => (n : ℤ)))
      ((Ioc 0 H).image (fun n : ℕ => -(n : ℤ))) := by
    apply disjoint_left.mpr
    intro j hj hk
    obtain ⟨n,hn,hnj⟩ := mem_image.mp hj
    obtain ⟨m,hm,hmj⟩ := mem_image.mp hk
    have hn0 := (mem_Ioc.mp hn).1
    have hm0 := (mem_Ioc.mp hm).1
    omega
  rw [nonzeroShortLags_eq, sum_union hd, sum_image, sum_image]
  · simp only [Int.natAbs_natCast,Int.natAbs_neg]
    ring
  · intro a _ b _ hab
    exact Int.ofNat_inj.mp (neg_injective hab)
  · intro a _ b _ hab
    exact Int.ofNat_inj.mp hab

theorem shortLag_singular_sum (H : ℕ) :
    (∑ j ∈ nonzeroShortLags H, singularFactor 24 j.natAbs) ≤
      (2*Real.exp 24)*(H : ℝ) := by
  rw [sum_shortLag_natAbs]
  have h := singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 H
  simp only [pow_one, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, mul_one] at h
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortLagRemoval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short additive lags have a uniformly small total contribution -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmetic_short_lags_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ H : ℕ, H ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ,
      (∀ n, ‖F n‖ ≤ 2) →
      |∑ j ∈ nonzeroShortLags H, kernelLagCorrelation B L τ C T N j F| ≤
        K*(H : ℝ)/(T : ℝ)+ε := by
  obtain ⟨K,hK,hbound⟩ := finite_kernelLagCorrelation_bound hFord hM
  refine ⟨8*K*Real.exp 24, by positivity, ?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs H hH ε hε
  have hJ : ∀ j ∈ nonzeroShortLags H, j ≠ 0 ∧ j.natAbs ≤ auxiliaryCutoff B := by
    intro j hj
    have h := mem_nonzeroShortLags.mp hj
    exact ⟨h.1,h.2.trans hH⟩
  filter_upwards [hB T hT hTs (nonzeroShortLags H) hJ ε hε] with N hN
  intro L τ C F hF
  apply (hN L τ C F hF).trans
  have h := mul_le_mul_of_nonneg_left (shortLag_singular_sum H)
    (show 0 ≤ 4*K/(T : ℝ) by positivity)
  have he : (4*K/(T : ℝ))*((2*Real.exp 24)*(H : ℝ)) =
      (8*K*Real.exp 24)*(H : ℝ)/(T : ℝ) := by ring
  rw [he] at h
  linarith only [h]

theorem graph_energy_eq_lag_correlations (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) :
    arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T) =
      ∑ j ∈ Icc (-(T : ℤ)) T, kernelLagCorrelation B L τ C T N j F := by
  rw [arithmeticOffDiagonalGraph_kernel, sum_comm]
  unfold kernelLagCorrelation
  rw [← sum_div]
  ring

theorem graph_short_lag_removal_identity (B L : ℕ) (τ C : ℝ)
    (T N H : ℕ) (hH : H ≤ T) (F : ℕ → ℂ) :
    arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T) -
      graphEnergyWithoutShortLags B L τ C T N H F =
        ∑ j ∈ nonzeroShortLags H, kernelLagCorrelation B L τ C T N j F := by
  have hsub : nonzeroShortLags H ⊆ Icc (-(T : ℤ)) T := by
    intro j hj
    have hh := (mem_nonzeroShortLags.mp hj).2.trans hH
    have hab : |j| ≤ (T : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hh
    exact mem_Icc.mpr (abs_le.mp hab)
  have hs := sum_sdiff hsub (f := fun j => kernelLagCorrelation B L τ C T N j F)
  rw [graph_energy_eq_lag_correlations]
  unfold graphEnergyWithoutShortLags
  linarith

theorem arithmetic_short_lags_removable
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ H : ℕ, H ≤ T → H ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ,
      (∀ n, ‖F n‖ ≤ 2) →
      |arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T) -
        graphEnergyWithoutShortLags B L τ C T N H F| ≤ K*(H : ℝ)/(T : ℝ)+ε := by
  obtain ⟨K,hK,hbound⟩ := arithmetic_short_lags_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs H hHT hHB ε hε
  filter_upwards [hB T hT hTs H hHB ε hε] with N hN
  intro L τ C F hF
  rw [graph_short_lag_removal_identity B L τ C T N H hHT F]
  exact hN L τ C F hF

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockEndpointLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint cost of averaging the actual graph over finite blocks -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem kernelLagCorrelation_zero (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (F : ℕ → ℂ) : kernelLagCorrelation B L τ C T N 0 F = 0 := by
  simp [kernelLagCorrelation, rawArithmeticGraphKernel_zero_lag]

theorem graph_without_short_nonzero (B L : ℕ) (τ C : ℝ)
    (T N H : ℕ) (F : ℕ → ℂ) :
    graphEnergyWithoutShortLags B L τ C T N H F =
      ∑ j ∈ nonzeroShortLags T \ nonzeroShortLags H,
        kernelLagCorrelation B L τ C T N j F := by
  classical
  unfold graphEnergyWithoutShortLags nonzeroShortLags
  have he : (Icc (-(T : ℤ)) T \ (Icc (-(H : ℤ)) H).erase 0).erase 0 =
      (Icc (-(T : ℤ)) T).erase 0 \ (Icc (-(H : ℤ)) H).erase 0 := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_sdiff]
    tauto
  rw [← he, sum_erase_eq_sub]
  · simp [kernelLagCorrelation_zero]
  · simp

theorem block_endpoint_loss_le (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) :
    |graphEnergyWithoutShortLags B L τ C T N H F -
      blockWeightedGraphEnergy B L τ C T N H M F| ≤
        ((T : ℝ)/M)*(∑ j ∈ nonzeroShortLags T,
          |kernelLagCorrelation B L τ C T N j F|) := by
  rw [graph_without_short_nonzero]
  unfold blockWeightedGraphEnergy
  rw [← sum_sub_distrib]
  have he (j : ℤ) : kernelLagCorrelation B L τ C T N j F -
      (1-(j.natAbs : ℝ)/M)*kernelLagCorrelation B L τ C T N j F =
      ((j.natAbs : ℝ)/M)*kernelLagCorrelation B L τ C T N j F := by ring
  simp_rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ nonzeroShortLags T \ nonzeroShortLags H,
        ((T : ℝ)/M)*|kernelLagCorrelation B L τ C T N j F| := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j.natAbs : ℝ)/M)]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
      exact_mod_cast (mem_nonzeroShortLags.mp (mem_sdiff.mp hj).1).2
    _ ≤ ∑ j ∈ nonzeroShortLags T,
        ((T : ℝ)/M)*|kernelLagCorrelation B L τ C T N j F| := by
      apply sum_le_sum_of_subset_of_nonneg sdiff_subset
      intro j _ _
      positivity
    _ = _ := (mul_sum ..).symm

theorem arithmetic_block_endpoint_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      T ≤ auxiliaryCutoff B → ∀ M : ℕ, T ≤ M →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ H L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 2) →
      |graphEnergyWithoutShortLags B L τ C T N H F -
        blockWeightedGraphEnergy B L τ C T N H M F| ≤ K*T/M+ε := by
  obtain ⟨K,hK,hbound⟩ := finite_kernelLagCorrelation_absolute_bound hFord hMertens
  refine ⟨8*K*Real.exp 24, by positivity, ?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs hTc M hTM ε hε
  have hJ : ∀ j ∈ nonzeroShortLags T, j ≠ 0 ∧ j.natAbs ≤ auxiliaryCutoff B := by
    intro j hj
    have h := mem_nonzeroShortLags.mp hj
    exact ⟨h.1,h.2.trans hTc⟩
  filter_upwards [hB T hT hTs (nonzeroShortLags T) hJ ε hε] with N hN
  intro H L τ C F hF
  have hmass := hN L τ C F hF
  have hs := mul_le_mul_of_nonneg_left (shortLag_singular_sum T)
    (show 0 ≤ 4*K/(T : ℝ) by positivity)
  have he : (4*K/(T : ℝ))*((2*Real.exp 24)*(T : ℝ)) = 8*K*Real.exp 24 := by
    field_simp
    ring
  rw [he] at hs
  have hmass' : (∑ j ∈ nonzeroShortLags T,
      |kernelLagCorrelation B L τ C T N j F|) ≤ 8*K*Real.exp 24+ε := by
    linarith only [hmass,hs]
  have hratio : (T : ℝ)/M ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hT.trans_le hTM : (0 : ℝ) < M)).mpr
    exact_mod_cast hTM
  calc
    _ ≤ ((T : ℝ)/M)*(∑ j ∈ nonzeroShortLags T,
        |kernelLagCorrelation B L τ C T N j F|) := block_endpoint_loss_le ..
    _ ≤ ((T : ℝ)/M)*(8*K*Real.exp 24+ε) :=
      mul_le_mul_of_nonneg_left hmass' (by positivity)
    _ ≤ (8*K*Real.exp 24)*T/M+ε := by
      have hh := mul_le_mul_of_nonneg_right hratio hε.le
      calc
        _ = (8*K*Real.exp 24)*T/M+((T : ℝ)/M)*ε := by ring
        _ ≤ _ := by linarith only [hh]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockCounting
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact counting of translated pairs inside integer blocks -/

namespace JointDickman
open Finset

theorem card_blockOverlap (M : ℕ) (j : ℤ) (hj : j.natAbs ≤ M) :
    (blockOverlap M j).card = M-j.natAbs := by
  have hab : |j| ≤ (M : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hj
  by_cases hsign : 0 ≤ j
  · have he : blockOverlap M j = Icc 1 ((M : ℤ)-j) := by
      ext i
      simp only [blockOverlap, mem_filter, mem_Icc]
      omega
    rw [he, Int.card_Icc]
    have ha : (j.natAbs : ℤ) = j := by rw [Int.natCast_natAbs,abs_of_nonneg hsign]
    omega
  · have he : blockOverlap M j = Icc (1-j) (M : ℤ) := by
      ext i
      simp only [blockOverlap, mem_filter, mem_Icc]
      omega
    rw [he, Int.card_Icc]
    have ha : (j.natAbs : ℤ) = -j := by
      rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hsign)]
    omega

theorem sum_block_origins (M V : ℕ) (i : ℤ) (hi : i ∈ Icc 1 (M : ℤ))
    (f : ℤ → ℝ) :
    (∑ s ∈ blockOrigins M V, if s+i ∈ Icc 1 (V : ℤ) then f (s+i) else 0) =
      ∑ n ∈ Icc 1 (V : ℤ), f n := by
  classical
  have he : (blockOrigins M V).filter (fun s => s+i ∈ Icc 1 (V : ℤ)) =
      (Icc 1 (V : ℤ)).image (fun n => n-i) := by
    ext s
    simp only [mem_filter, blockOrigins, mem_Icc, mem_image]
    constructor
    · rintro ⟨hs,hn⟩
      exact ⟨s+i,hn,by omega⟩
    · rintro ⟨n,hn,he⟩
      have h := mem_Icc.mp hi
      constructor <;> omega
  rw [← sum_filter, he, sum_image]
  · simp
  · intro a _ b _ hab
    dsimp at hab
    omega

theorem sum_block_overlap (M V : ℕ) (j : ℤ) (hj : j.natAbs ≤ M)
    (f : ℤ → ℝ) :
    (∑ s ∈ blockOrigins M V, ∑ i ∈ blockOverlap M j,
      if s+i ∈ Icc 1 (V : ℤ) then f (s+i) else 0) =
        ((M-j.natAbs : ℕ) : ℝ)*(∑ n ∈ Icc 1 (V : ℤ), f n) := by
  rw [sum_comm]
  have he (i : ℤ) (hi : i ∈ blockOverlap M j) :=
    sum_block_origins M V i (mem_filter.mp hi).1 f
  simp_rw [sum_congr rfl he]
  simp only [sum_const, nsmul_eq_mul, card_blockOverlap M j hj]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact block averaging and reindexing into square matrices -/

namespace JointDickman
open Finset

theorem finiteBlockAverage_eq (M V : ℕ) (hM : 0 < M)
    (J : Finset ℤ) (hJ : ∀ j ∈ J, j.natAbs ≤ M) (K : ℤ → ℤ → ℝ) :
    finiteBlockAverage M V J K =
      ∑ j ∈ J, (1-(j.natAbs : ℝ)/M)*(∑ n ∈ Icc 1 (V : ℤ), K j n) := by
  unfold finiteBlockAverage
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [sum_block_overlap M V j (hJ j hj), Nat.cast_sub (hJ j hj)]
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticBlockAverage
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite block expression for the arithmetic graph energy -/

namespace JointDickman
open Finset

theorem sum_int_Icc_toNat (V : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 (V : ℤ), f n.toNat) = ∑ n ∈ Icc 1 V, f n := by
  apply sum_bij (fun n _ => n.toNat)
  · intro n hn
    have h := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n hn m hm he
    have hn' := mem_Icc.mp hn
    have hm' := mem_Icc.mp hm
    omega
  · intro n hn
    refine ⟨(n : ℤ),?_,by simp⟩
    have h := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n _
    rfl

theorem sum_arithmeticVertexCorrelation (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) (j : ℤ) :
    (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ),
      arithmeticVertexCorrelation B L τ C T N F j n) =
        kernelLagCorrelation B L τ C T N j F := by
  unfold arithmeticVertexCorrelation
  rw [sum_int_Icc_toNat (arithmeticGraphVertexCap B N) (fun n : ℕ =>
    (rawArithmeticGraphKernel B L τ C T N j n *
      (star (F n)*F ((n : ℤ)+j).toNat).re)/((B : ℝ)*T*N)), ← sum_div]
  rfl

theorem arithmeticBlockAverage_eq_weighted (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (hM : 0 < M) (hTM : T ≤ M) (F : ℕ → ℂ) :
    arithmeticBlockAverage B L τ C T N H M F =
      blockWeightedGraphEnergy B L τ C T N H M F := by
  unfold arithmeticBlockAverage blockWeightedGraphEnergy
  rw [finiteBlockAverage_eq M _ hM]
  · simp_rw [sum_arithmeticVertexCorrelation]
  · intro j hj
    exact ((mem_nonzeroShortLags.mp (mem_sdiff.mp hj).1).2).trans hTM

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockEnergyApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform error in replacing graph energy by its finite block average -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmetic_block_energy_approximation
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      T ≤ auxiliaryCutoff B → ∀ H M : ℕ, H ≤ T → T ≤ M →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 2) →
      |arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T) -
        arithmeticBlockAverage B L τ C T N H M F| ≤
          K*((H : ℝ)/T+(T : ℝ)/M)+ε := by
  obtain ⟨Ks,hKs,hshort⟩ := arithmetic_short_lags_removable hFord hMertens
  obtain ⟨Kb,hKb,hblock⟩ := arithmetic_block_endpoint_bound hFord hMertens
  refine ⟨Ks+Kb,add_pos hKs hKb,?_⟩
  filter_upwards [hshort,hblock] with B hBshort hBblock
  intro T hT hTs hTc H M hHT hTM ε hε
  filter_upwards [hBshort T hT hTs H hHT (hHT.trans hTc) (ε/2) (half_pos hε),
    hBblock T hT hTs hTc M hTM (ε/2) (half_pos hε)] with N hNs hNb
  intro L τ C F hF
  rw [arithmeticBlockAverage_eq_weighted B L τ C T N H M (hT.trans_le hTM) hTM F]
  have h1 := hNs L τ C F hF
  have h2 := hNb H L τ C F hF
  have hab := abs_sub_le (arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T))
    (graphEnergyWithoutShortLags B L τ C T N H F)
    (blockWeightedGraphEnergy B L τ C T N H M F)
  have hcross1 : 0 ≤ Kb*((H : ℝ)/T) := by positivity
  have hcross2 : 0 ≤ Ks*((T : ℝ)/M) := by positivity
  have hsum : Ks*(H : ℝ)/T+ε/2+(Kb*(T : ℝ)/M+ε/2) ≤
      (Ks+Kb)*((H : ℝ)/T+(T : ℝ)/M)+ε := by
    calc
      _ ≤ Ks*(H : ℝ)/T+ε/2+(Kb*(T : ℝ)/M+ε/2)+
          (Kb*((H : ℝ)/T)+Ks*((T : ℝ)/M)) := by linarith only [hcross1,hcross2]
      _ = _ := by ring
  exact hab.trans ((add_le_add h1 h2).trans hsum)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PositiveBlockEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive graph energy survives the exact passage to blocks -/

namespace JointDickman
open Filter
open scoped Topology

theorem block_scale_error_le (A T : ℕ) (hT : 0 < T) :
    (((T/A : ℕ) : ℝ)/(T : ℝ)+(T : ℝ)/(A*T : ℕ)) ≤ 2/(A : ℝ) := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hfloor := div_le_div_of_nonneg_right
    (Nat.cast_div_le (m := T) (n := A) : ((T/A : ℕ) : ℝ) ≤ (T : ℝ)/A)
    (Nat.cast_nonneg T)
  have he1 : ((T : ℝ)/A)/T = 1/(A : ℝ) := by field_simp
  have he2 : (T : ℝ)/(A*T : ℕ) = 1/(A : ℝ) := by push_cast; field_simp
  rw [he1] at hfloor
  rw [he2]
  rw [show (2 : ℝ)/(A : ℝ) = 1/(A : ℝ)+1/(A : ℝ) by ring]
  linarith only [hfloor]

theorem positive_blocks_of_graph_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {e : ℝ} (he : 0 < e) :
    ∃ A : ℕ, 0 < A ∧ ∀ (L : ℕ) (τ C : ℝ) (r : ℕ → ℕ), StrictMono r →
      ∀ F : ℕ → ℕ → ℂ, (∀ N n, ‖F N n‖ ≤ 2) →
      (∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        e ≤ arithmeticOffDiagonalGraph B L τ C (amplificationMultiplier B) (r N) (F (r N)) /
          ((B : ℝ)*amplificationMultiplier B)) →
      ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        e/2 ≤ arithmeticBlockAverage B L τ C (amplificationMultiplier B) (r N)
          (amplificationMultiplier B/A) (A*amplificationMultiplier B) (F (r N)) := by
  obtain ⟨K,hK,happrox⟩ := arithmetic_block_energy_approximation hFord hMertens
  obtain ⟨A,hA⟩ := exists_nat_gt (max (1 : ℝ) (8*K/e))
  have hA1 : (1 : ℝ) < A := lt_of_le_of_lt (le_max_left _ _) hA
  have hApos : 0 < A := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hA1)
  have hAlarge : 8*K/e < (A : ℝ) := lt_of_le_of_lt (le_max_right _ _) hA
  have herror : K*(2/(A : ℝ)) < e/4 := by
    have hAreal : (0 : ℝ) < A := by exact_mod_cast hApos
    have hprod := (div_lt_iff₀ he).mp hAlarge
    have hh : 8*K/(A : ℝ) < e := (div_lt_iff₀ hAreal).mpr (by nlinarith only [hprod])
    calc
      _ = (8*K/(A : ℝ))/4 := by ring
      _ < e/4 := div_lt_div_of_pos_right hh (by norm_num)
  refine ⟨A,hApos,?_⟩
  intro L τ C r hr F hF hgraph
  filter_upwards [happrox,hgraph,amplificationMultiplier_valid,
    amplificationMultiplier_le_cutoff] with B hB hGraph hT hTc
  let T := amplificationMultiplier B
  have hTM : T ≤ A*T := by nlinarith [hApos]
  have happ := hB T hT.1 hT.2 hTc (T/A) (A*T) (Nat.div_le_self _ _) hTM
    (e/4) (by positivity)
  filter_upwards [hr.tendsto_atTop.eventually happ,hGraph] with N hN hGN
  have hbound := hN L τ C (F (r N)) (hF (r N))
  have hscale := mul_le_mul_of_nonneg_left (block_scale_error_le A T hT.1) hK.le
  have hdiff := (le_abs_self
    (arithmeticOffDiagonalGraph B L τ C T (r N) (F (r N))/((B : ℝ)*T) -
      arithmeticBlockAverage B L τ C T (r N) (T/A) (A*T) (F (r N)))).trans hbound
  change e ≤ arithmeticOffDiagonalGraph B L τ C T (r N) (F (r N))/((B : ℝ)*T) at hGN
  linarith only [hdiff,hGN,hscale,herror]

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.positive_blocks_of_graph_jd_oai := @OAI.JointDickman.positive_blocks_of_graph_jd_oai
