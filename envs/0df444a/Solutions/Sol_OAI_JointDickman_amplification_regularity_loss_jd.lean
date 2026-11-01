-- Prove2me | solution 1 for OAI.JointDickman.amplification_regularity_loss_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:23:42.528209+00:00
-- url     : https://prove2.me/submissions/657de275-7624-484a-ac80-349d9e1313d4

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

theorem primeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    primeProductMass P z n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq =>
    hn (Finset.mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairPushforward
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pushforward for two independent prime products -/

namespace JointDickman

open Finset

theorem primeProductPair_weighted_sum (P : Finset ℕ) (z : ℝ)
    (S : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (∑ ac ∈ S, f ac * (primeProductMass P z ac.1 * primeProductMass P z ac.2)) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ S then
          f (∏ p ∈ A, p, ∏ p ∈ D, p) *
            (bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D)
        else 0 := by
  classical
  unfold primeProductMass
  simp_rw [sum_mul_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  have hpoint (ac : ℕ × ℕ) :
      f ac * ((if (∏ p ∈ A, p) = ac.1 then bernoulliSubsetMass P (fun p => z / p) A else 0) *
        (if (∏ p ∈ D, p) = ac.2 then bernoulliSubsetMass P (fun p => z / p) D else 0)) =
      if ac = (∏ p ∈ A, p, ∏ p ∈ D, p) then
        f ac * (bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D)
      else 0 := by
    rcases ac with ⟨a, c⟩
    by_cases ha : (∏ p ∈ A, p) = a <;> by_cases hc : (∏ p ∈ D, p) = c
    all_goals simp only [ha, hc, ite_true, if_true, ite_false, if_false, zero_mul, mul_zero, Prod.mk.injEq]
    all_goals simp_all only [eq_comm, and_self, and_true, and_false, ite_false, if_false]
  simp_rw [hpoint]
  simp

theorem primeProductPair_sum_event (P : Finset ℕ) (z : ℝ) (S : Finset (ℕ × ℕ)) :
    (∑ ac ∈ S, primeProductMass P z ac.1 * primeProductMass P z ac.2) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ S then
          bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D
        else 0 := by
  simpa only [one_mul] using primeProductPair_weighted_sum P z S (fun _ => 1)

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeMassApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the local odds correction from prime-product masses

For every event, the independent-subset mass differs from the uncorrected
Euler weight by at most the sum of squared selection probabilities.
The resulting prime-tail error is uniform over events.
-/

namespace JointDickman

open Finset

theorem uncorrectedSubsetMass_identity {P S : Finset ℕ} (q : ℕ → ℝ) (hS : S ⊆ P) :
    uncorrectedSubsetMass P q S = bernoulliSubsetMass P q S * ∏ p ∈ S, (1 - q p) := by
  unfold uncorrectedSubsetMass bernoulliSubsetMass
  rw [← prod_sdiff hS (f := fun p => 1 - q p)]
  ring

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

theorem uncorrectedSubsetMass_harmonic {P S E : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (hE : Disjoint S E) :
    uncorrectedSubsetMass P (fun p => z / p) S =
      primeNormalizer P z * roughSquarefreeWeight E z (∏ p ∈ S, p) / (∏ p ∈ S, p : ℕ) := by
  have hSP : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hrough : roughSquarefreeWeight E z (∏ p ∈ S, p) = z ^ S.card := by
    simp only [roughSquarefreeWeight, ArithmeticFunction.coe_mk, Nat.primeFactors_prod hSP,
      hE, ite_eq_left, squarefreeWeight, primeProduct_squarefree S hSP,
      primeProduct_cardFactors S hSP]
  rw [hrough]
  simp only [uncorrectedSubsetMass, primeNormalizer, prod_div_distrib, prod_const, Nat.cast_prod]
  ring

theorem uncorrectedPrimeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    uncorrectedPrimeProductMass P z (∏ p ∈ S, p) = uncorrectedSubsetMass P (fun p => z / p) S := by
  classical
  unfold uncorrectedPrimeProductMass
  rw [sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (mem_powerset.mpr hS))

theorem uncorrectedPrimeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    uncorrectedPrimeProductMass P z n = 0 := by
  classical
  apply sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq => hn (mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

theorem uncorrectedPrimeProductMass_harmonic {U : ℝ} {N n : ℕ}
    (hnU : (n : ℝ) ≤ U) (z : ℝ) :
    uncorrectedPrimeProductMass (largePrimeSet U N) z n =
      primeNormalizer (largePrimeSet U N) z * roughSquarefreeWeight (Nat.primesLE N) z n / n := by
  classical
  let P := largePrimeSet U N
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  by_cases hn : n ∈ P.powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hn
    have hS : S ⊆ P := mem_powerset.mp hSP
    have hd : Disjoint S (Nat.primesLE N) := by
      apply disjoint_left.mpr
      intro p hp hsmall
      have hgt : (N : ℝ) < p := (mem_filter.mp (hS hp)).2
      have hle : p ≤ N := (Nat.mem_primesLE.mp hsmall).1
      exact (not_lt_of_ge (by exact_mod_cast hle)) hgt
    rw [← hSn, uncorrectedPrimeProductMass_at_product z hP hS]
    exact uncorrectedSubsetMass_harmonic z hP hS hd
  · rw [uncorrectedPrimeProductMass_eq_zero z n hn]
    by_cases hd : Disjoint n.primeFactors (Nat.primesLE N)
    · by_cases hsq : Squarefree n
      · have hsub : n.primeFactors ⊆ P := by
          intro p hp
          have hpprime := Nat.prime_of_mem_primeFactors hp
          have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
          have hpU : (p : ℝ) ≤ U := (by exact_mod_cast hpn : (p : ℝ) ≤ n).trans hnU
          have hpN : N < p := by
            by_contra hnot
            exact disjoint_left.mp hd hp (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
          exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpU, hpprime⟩, by exact_mod_cast hpN⟩
        exact False.elim (hn (mem_image.mpr ⟨n.primeFactors, mem_powerset.mpr hsub,
          Nat.prod_primeFactors_of_squarefree hsq⟩))
      · simp [roughSquarefreeWeight, hd, squarefreeWeight, hsq]
    · simp [roughSquarefreeWeight, hd]

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
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- The simultaneous prescribed-root count is exactly the product of the
local root counts, including an empty family of moduli. -/
theorem crt_root_period_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i))) :
    (∑ n ∈ range (∏ i, m i),
      if ∀ i, (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) =
      ∏ i, ((A i).card : ℝ) := by
  classical
  have hind (n : ℕ) : (∏ i, if (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) =
      if ∀ i, (n : ZMod (m i)) ∈ A i then 1 else 0 := by
    split_ifs with h
    · exact prod_eq_one (fun i _ => ite_eq_left (h i))
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [← hind]
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  rw [crt_period_sum m hm hcop (fun i a => if a ∈ A i then (1 : ℝ) else 0)]
  apply prod_congr rfl
  intro i _
  let : NeZero (m i) := ⟨(hm i).ne'⟩
  simp

/-- An interval intersection has at most two errors per simultaneous
residue class, independent of the modulus and the interval location. -/
theorem crt_root_interval_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i))) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, if ∀ i, (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ∏ i, ((A i).card : ℝ) / (m i)| ≤
        2 * ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hM : 0 < ∏ i, m i := prod_pos (fun i _ => hm i)
  let : NeZero (∏ i, m i) := ⟨hM.ne'⟩
  let e := ZMod.prodEquivPi m hcop
  let F := fun n : ZMod (∏ i, m i) => if ∀ i, e n i ∈ A i then (1 : ℝ) else 0
  have hF (n : ℕ) : F n = if ∀ i, (n : ZMod (m i)) ∈ A i then 1 else 0 := by
    have heval : e (n : ZMod (∏ i, m i)) = (n : ∀ i, ZMod (m i)) := map_natCast e n
    simp [F, heval]
  have hmass : (∑ n ∈ range (∏ i, m i), F n) = ∏ i, ((A i).card : ℝ) := by
    simp_rw [hF]
    exact crt_root_period_count m hm hcop A
  have h := nonnegative_periodic_interval_error hM F
    (fun n => by dsimp [F]; split_ifs <;> norm_num) hab
  rw [hmass] at h
  simp_rw [hF] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  rw [prod_div_distrib, Nat.cast_prod]
  ring

/-- Specialization to a finite set of distinct primes. -/
theorem prime_root_interval_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p)) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, if ∀ p ∈ P, (n : ZMod p) ∈ A p then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ∏ p ∈ P, ((A p).card : ℝ) / p| ≤
        2 * ∏ p ∈ P, ((A p).card : ℝ) := by
  have hcop : Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have h := crt_root_interval_error (fun p : P => (p : ℕ))
    (fun p => (hP p p.property).pos) hcop (fun p => A p) hab
  simpa only [P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ) / p),
    P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ)), Subtype.forall] using h

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

/-- The same level bound with arbitrary local root counts bounded by `k`. -/
theorem sieve_level_root_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (k N : ℕ) (hr : ∀ p ∈ P, r p ≤ k) :
    (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N), ∏ p ∈ D, r p) ≤
      (N + 1) * N ^ k := by
  apply le_trans _ (sieve_level_power_sum P hP k N)
  apply sum_le_sum
  intro D hD
  calc
    _ ≤ ∏ _p ∈ D, k := prod_le_prod' (fun p hp =>
      hr p (mem_powerset.mp (mem_filter.mp hD).1 hp))
    _ = _ := by simp

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveInterval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The interval sieve with its actual arithmetic remainder -/

namespace JointDickman

open Finset

/-- CRT evaluates the actual remainder used by the upper sieve. -/
theorem root_sieve_remainder (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p)) {a b : ℕ} (hab : a ≤ b)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder (fun n : Ico a b => rootEvents P A n) (fun _ => 1)
      ((b : ℝ) - a) (fun p => ((A p).card : ℝ) / p) D| ≤
        2 * ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  have hcond (n : Ico a b) : D ⊆ rootEvents P A n ↔
      ∀ p ∈ D, (n.val : ZMod p) ∈ A p := by
    constructor
    · intro h p hp
      exact (mem_filter.mp (h hp)).2
    · intro h p hp
      exact mem_filter.mpr ⟨hD hp, h p hp⟩
  have hid : sieveRemainder (fun n : Ico a b => rootEvents P A n) (fun _ => 1)
      ((b : ℝ) - a) (fun p => ((A p).card : ℝ) / p) D =
      (∑ n ∈ Ico a b, if ∀ p ∈ D, (n : ZMod p) ∈ A p then (1 : ℝ) else 0) -
        ((b : ℝ) - a) * ∏ p ∈ D, ((A p).card : ℝ) / p := by
    unfold sieveRemainder sieveIntersection
    simp_rw [hcond]
    rw [(Ico a b).sum_coe_sort (fun n : ℕ =>
      if ∀ p ∈ D, (n : ZMod p) ∈ A p then (1 : ℝ) else 0)]
  rw [hid]
  exact prime_root_interval_error D (fun p hp => hP p (hD hp)) A hab

/-- Uniform weighted interval bound, derived from Ford and Mertens. -/
theorem weighted_interval_sieve (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
      (θ : ℕ → ℝ) (a b : ℕ) (z : ℝ), a ≤ b → 2 ≤ z →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, ((A p).card : ℝ) ≤ k) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico a b, ∏ p ∈ rootEvents P A n, θ p) ≤
        C * ((b : ℝ) - a) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / p + ((A p).card : ℝ) / p * θ p)) +
        2 * ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
          ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_upper_sieve_from_published hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P A θ a b z hab hz hP hA hθ
  let E := fun n : Ico a b => rootEvents P A n
  let g := fun p => ((A p).card : ℝ) / p
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    dsimp [g]
    refine ⟨by positivity, ?_, div_le_div_of_nonneg_right (hA p hp) hp0.le⟩
    apply (div_le_iff₀ hp0).mpr
    linarith [(hP p hp).2.2, hA p hp]
  have h := hbound (Ico a b) P E (fun _ => 1) ((b : ℝ) - a) z g θ hz
    (sub_nonneg.mpr (by exact_mod_cast hab)) (by intros; norm_num)
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
    (fun n => filter_subset _ _) hg hθ
  simp only [one_mul] at h
  dsimp only [E, g] at h
  rw [(Ico a b).sum_coe_sort (fun n : ℕ => ∏ p ∈ rootEvents P A n, θ p)] at h
  apply h.trans
  apply add_le_add le_rfl
  rw [mul_sum]
  apply sum_le_sum
  intro D hD
  exact root_sieve_remainder P (fun p hp => (hP p hp).1) A hab
    (mem_powerset.mp (mem_filter.mp hD).1)

/-- A completely explicit polynomial remainder suffices at a small fixed
power cutoff. All interval positions and reducing weights are uniform. -/
theorem weighted_interval_sieve_polynomial
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
      (θ : ℕ → ℝ) (a b Z : ℕ), a ≤ b → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, (A p).card ≤ k) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico a b, ∏ p ∈ rootEvents P A n, θ p) ≤
        C * ((b : ℝ) - a) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / p + ((A p).card : ℝ) / p * θ p)) +
        2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  obtain ⟨C, hC, hbound⟩ := weighted_interval_sieve hFord hM
    (show (0 : ℝ) < k by exact_mod_cast hk)
  refine ⟨C, hC, ?_⟩
  intro P A θ a b Z hab hZ hP hA hθ
  have h := hbound P A θ a b Z hab (by exact_mod_cast hZ)
    (fun p hp => ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2.1,
      by exact_mod_cast (hP p hp).2.2⟩)
    (fun p hp => by exact_mod_cast hA p hp) hθ
  apply h.trans
  apply add_le_add le_rfl
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have heq : P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ (Z : ℝ)) =
      P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z) := by
    ext D
    simp only [mem_filter, Nat.cast_le]
  rw [heq]
  exact_mod_cast sieve_level_root_sum P (fun p hp => (hP p hp).1)
    (fun p => (A p).card) k Z hA

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ThreeFormLocalBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

theorem regularCoefficientWeight_nonneg (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    0 ≤ regularCoefficientWeight B L τ C n := by
  unfold regularCoefficientWeight
  split_ifs
  · exact coefficientWeight_nonneg _ _
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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TiltedCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential prime-count tilts of the actual coefficient -/

namespace JointDickman

open Finset

theorem coefficient_prefix_count {B n : ℕ} (hn : n ≠ 0) (g : ℝ) :
    (primePrefix B g (coefficientPrimeSet B n)).card =
      primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) n := by
  rw [coefficientPrimeSet_eq_inter hn, primePrefix_inter]
  rfl

theorem coefficient_tail_count {B n : ℕ} (hn : n ≠ 0) (Y : ℝ) :
    ((coefficientPrimeSet B n).filter (fun p : ℕ => Y < Real.log p)).card =
      primeDivisorCount ((auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) n := by
  classical
  rw [coefficientPrimeSet_eq_inter hn]
  congr 1
  ext p
  simp only [mem_filter, mem_inter]
  tauto

theorem tiltedPrimeWeight_bounds (Q : Finset ℕ) {s : ℝ} (hs : Real.exp s ≤ 2) (p : ℕ) :
    0 ≤ tiltedPrimeWeight Q s p ∧ tiltedPrimeWeight Q s p ≤ 1 := by
  unfold tiltedPrimeWeight
  split_ifs <;> constructor <;> nlinarith [Real.exp_pos s]

theorem tiltedSieveTheta_bounds (P : ℕ) (Q : Finset ℕ) {s : ℝ} (hs : Real.exp s ≤ 2) (p : ℕ) :
    0 ≤ tiltedSieveTheta P Q s p ∧ tiltedSieveTheta P Q s p ≤ 1 := by
  unfold tiltedSieveTheta
  split_ifs
  · norm_num
  · exact tiltedPrimeWeight_bounds Q hs p

theorem tilted_prime_product (S Q : Finset ℕ) (s : ℝ) :
    (∏ p ∈ S, tiltedPrimeWeight Q s p) =
      (1 / 2 : ℝ) ^ S.card * Real.exp (s * (S ∩ Q).card) := by
  classical
  have heq (p : ℕ) : tiltedPrimeWeight Q s p =
      (1 / 2 : ℝ) * (if p ∈ Q then Real.exp s else 1) := by
    by_cases hp : p ∈ Q <;> simp [tiltedPrimeWeight, hp]
  have hfilter : S.filter (fun p => p ∈ Q) = S ∩ Q := by ext p; simp
  simp_rw [heq]
  rw [prod_mul_distrib, prod_const, ← prod_filter, hfilter, prod_const, ← Real.exp_nat_mul]
  congr 2; ring

theorem tiltedCoefficientWeight_le_sieved (B Z : ℕ) (Q : Finset ℕ) {s : ℝ}
    (hs : Real.exp s ≤ 2) (n : ℕ) :
    tiltedCoefficientWeight B Q s n ≤ coefficientScale B *
      ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) := by
  classical
  have hnonneg : 0 ≤ coefficientScale B *
      ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) :=
    mul_nonneg (coefficientScale_nonneg _) (prod_nonneg (fun p _ =>
      residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q hs p).1))
  by_cases hd : Disjoint n.primeFactors (Nat.primesLE (auxiliaryCutoff B))
  · by_cases hsq : Squarefree n
    · have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
        calc
          _ = ArithmeticFunction.cardFactors (∏ p ∈ n.primeFactors, p) :=
            congrArg ArithmeticFunction.cardFactors (Nat.prod_primeFactors_of_squarefree hsq).symm
          _ = _ := primeProduct_cardFactors _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
      have heq (p : ℕ) (hp : p ∈ sievePrimes Z) :
          residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) =
            if p ∣ n then tiltedPrimeWeight Q s p else 1 := by
        have hpprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        by_cases hpn : p ∣ n
        · have hpP : ¬p ≤ auxiliaryCutoff B := by
            intro h
            exact disjoint_left.mp hd (hpprime.mem_primeFactors hpn hsq.ne_zero)
              (Nat.mem_primesLE.mpr ⟨h, hpprime⟩)
          simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn, tiltedSieveTheta, hpP]
        · simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn]
      have hsub : (sievePrimes Z).filter (fun p => p ∣ n) ⊆ n.primeFactors := by
        intro p hp
        have hmem := mem_filter.mp hp
        exact (Nat.mem_primesLE.mp (mem_filter.mp hmem.1).1).2.mem_primeFactors hmem.2 hsq.ne_zero
      have hprod : (∏ p ∈ n.primeFactors, tiltedPrimeWeight Q s p) ≤
          ∏ p ∈ (sievePrimes Z).filter (fun p => p ∣ n), tiltedPrimeWeight Q s p :=
        prod_le_prod_of_subset_of_le_one hsub
          (fun p _ => (tiltedPrimeWeight_bounds Q hs p).1)
          (fun p _ _ => (tiltedPrimeWeight_bounds Q hs p).2)
      have htprod := tilted_prime_product n.primeFactors Q s
      rw [htprod] at hprod
      have hbound := mul_le_mul_of_nonneg_left hprod (coefficientScale_nonneg B)
      simpa only [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight,
        ArithmeticFunction.coe_mk, ite_eq_left hd, squarefreeWeight, ite_eq_left hsq,
        hcard, primeDivisorCount, mul_assoc, prod_congr rfl heq, ← prod_filter] using hbound
    · simpa [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight, squarefreeWeight, hd, hsq] using hnonneg
  · simpa [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight, hd] using hnonneg

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TiltedSieveDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler-product cost of an exponential prime-count tilt -/

namespace JointDickman

open Finset

theorem tilted_sieve_density_bound (P Z : ℕ) (Q : Finset ℕ) {s : ℝ}
    (hs : Real.exp s ≤ 2) :
    tiltedSieveDensity P Z Q s ≤ roughSieveDensity P Z *
      Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4) := by
  classical
  let S := sievePrimes Z
  let x := fun p => (1 - tiltedSieveTheta P Q s p) / (p : ℝ)
  let y := roughSieveRate P
  have hp (p : ℕ) (h : p ∈ S) : p.Prime := (Nat.mem_primesLE.mp (mem_filter.mp h).1).2
  have hx (p : ℕ) (h : p ∈ S) : 0 ≤ x p ∧ x p ≤ 1 / 2 := by
    have htheta := tiltedSieveTheta_bounds P Q hs p
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    dsimp [x]
    constructor
    · exact div_nonneg (by linarith) hp0.le
    · apply (div_le_iff₀ hp0).mpr
      linarith
  have hy (p : ℕ) (h : p ∈ S) : 0 ≤ y p ∧ y p ≤ 1 / 2 := by
    have hb := roughSieveRate_bounds P p (hp p h)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    exact ⟨hb.1, hb.2.1.trans (one_div_le_one_div_of_le (by norm_num) hp2)⟩
  have hquad (f : ℕ → ℝ) (hf : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ 1 / (p : ℝ)) :
      ∑ p ∈ S, f p ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ S, 1 / (p : ℝ) ^ 2 := by
        apply sum_le_sum
        intro p h
        simpa only [one_div_pow] using pow_le_pow_left₀ (hf p h).1 (hf p h).2 2
      _ ≤ 1 := by
        simpa using sum_reciprocal_square_tail S (by norm_num : (1 : ℕ) ≠ 0)
          (fun p h => (hp p h).one_lt)
  have hxq := hquad x (fun p h => ⟨(hx p h).1, by
    dsimp [x]
    exact div_le_div_of_nonneg_right (by linarith [(tiltedSieveTheta_bounds P Q hs p).1]) (Nat.cast_nonneg p)⟩)
  have hyq := hquad y (fun p h => ⟨(hy p h).1, (roughSieveRate_bounds P p (hp p h)).2.1⟩)
  have hxe := finite_log_product_error S x hx
  have hye := finite_log_product_error S y hy
  have hlin : (∑ p ∈ S, y p) - (∑ p ∈ S, x p) =
      ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q := by
    rw [← sum_sub_distrib]
    unfold tiltPrimeReciprocalMass
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro p h
    by_cases hP : p ≤ P
    · have hn : ¬P < p := by omega
      simp [x, y, roughSieveRate, roughSieveTheta, tiltedSieveTheta, hP, hn]
    · have hP' : P < p := by omega
      by_cases hQ : p ∈ Q <;>
        simp [x, y, roughSieveRate, roughSieveTheta, tiltedSieveTheta, tiltedPrimeWeight, hP, hP', hQ]
      ring
  have hlog : Real.log (∏ p ∈ S, (1 - x p)) ≤
      Real.log (∏ p ∈ S, (1 - y p)) +
        ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4 := by
    have hxe' := (abs_le.mp hxe).2
    have hye' := (abs_le.mp hye).1
    linarith
  have hxprod : 0 < ∏ p ∈ S, (1 - x p) :=
    prod_pos (fun p h => by linarith [(hx p h).2])
  have hyprod : 0 < ∏ p ∈ S, (1 - y p) :=
    prod_pos (fun p h => by linarith [(hy p h).2])
  calc
    _ = Real.exp (Real.log (∏ p ∈ S, (1 - x p))) := (Real.exp_log hxprod).symm
    _ ≤ Real.exp (Real.log (∏ p ∈ S, (1 - y p)) +
        ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [add_assoc, Real.exp_add, Real.exp_log hyprod]; rfl

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MarkovRemainders
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the Markov multipliers on sieve remainders -/

namespace JointDickman

open Filter
open scoped Topology

theorem auxiliaryLogLength_between :
    ∀ᶠ B : ℕ in atTop, 0 ≤ auxiliaryLogLength B ∧ auxiliaryLogLength B ≤ Real.log B := by
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [auxiliaryLogLength_tendsto.eventually_ge_atTop 0,
    hloglarge, eventually_gt_atTop 1] with B hℓ hlog hB
  refine ⟨hℓ, ?_⟩
  have hr : auxiliaryRatio B = (B : ℝ) / Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    rfl
  have hRB : auxiliaryRatio B ≤ B := by
    rw [hr]
    exact div_le_self (Nat.cast_nonneg _) hlog
  exact Real.log_le_log (auxiliaryRatio_pos hB) hRB

theorem prefix_markov_multiplier_bounds {B : ℕ} {g τ s : ℝ}
    (hB : 1 ≤ B) (hg : 0 ≤ g) (hg1 : g ≤ 1) (hτ : 0 ≤ τ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hℓ : 0 ≤ auxiliaryLogLength B) (hℓlog : auxiliaryLogLength B ≤ Real.log B) :
    Real.exp (-s * ((g / 2 + τ) * auxiliaryLogLength B)) ≤ B ∧
    Real.exp (s * ((g / 2 - τ) * auxiliaryLogLength B)) ≤ B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  have hexp : Real.exp (Real.log B) = B := Real.exp_log hB0
  constructor
  · have hexponent : -s * ((g / 2 + τ) * auxiliaryLogLength B) ≤ Real.log B := by
      have hm := mul_nonneg hs (mul_nonneg (by linarith : 0 ≤ g / 2 + τ) hℓ)
      nlinarith
    exact (Real.exp_le_exp.mpr hexponent).trans_eq hexp
  · have hscoeff : s * (g / 2 - τ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (show g / 2 - τ ≤ 1 by linarith) hs
      nlinarith
    have h := mul_le_mul_of_nonneg_right hscoeff hℓ
    have hexponent : s * ((g / 2 - τ) * auxiliaryLogLength B) ≤ Real.log B := by nlinarith
    exact (Real.exp_le_exp.mpr hexponent).trans_eq hexp

theorem tail_markov_multiplier_bound {B Y C : ℝ} (hB : 1 ≤ B) (hY : 1 ≤ Y) (hC : 0 ≤ C) :
    Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C)) ≤ B := by
  have hB0 : 0 < B := by linarith
  have hY0 : 0 < Y := by linarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hdiv : B / Y ≤ B := div_le_self hB0.le hY
  have hlogdiv := Real.log_le_log (div_pos hB0 hY0) hdiv
  have hexponent : (1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C) ≤ Real.log B := by linarith
  exact (Real.exp_le_exp.mpr hexponent).trans_eq (Real.exp_log hB0)

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCountTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Markov bounds for prime counts in the actual coefficient sums -/

namespace JointDickman

open Finset

theorem weighted_exp_markov {α : Type*} (S : Finset α) (w N : α → ℝ) (s r : ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) :
    (∑ x ∈ S, if s * r ≤ s * N x then w x else 0) ≤
      Real.exp (-s * r) * ∑ x ∈ S, w x * Real.exp (s * N x) := by
  classical
  rw [mul_sum]
  apply sum_le_sum
  intro x hx
  have hwx := hw x hx
  by_cases h : s * r ≤ s * N x
  · rw [ite_eq_left h]
    have he : 1 ≤ Real.exp (-s * r) * Real.exp (s * N x) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    have hh := mul_le_mul_of_nonneg_left he (hw x hx)
    nlinarith
  · rw [ite_eq_right h]
    positivity

open Filter
open scoped Topology

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

/-- Finite summation of a common main factor and uniformly bounded remainders. -/
theorem sum_le_linear_remainder {ι : Type*} (S : Finset ι)
    (f t r : ι → ℝ) {A E R : ℝ} (hE : 0 ≤ E)
    (hf : ∀ i ∈ S, f i ≤ A * t i + r i * E)
    (hr : ∀ i ∈ S, r i ≤ R) :
    (∑ i ∈ S, f i) ≤ A * (∑ i ∈ S, t i) + (S.card : ℝ) * R * E := by
  calc
    _ ≤ ∑ i ∈ S, (A * t i + R * E) := sum_le_sum (fun i hi =>
      (hf i hi).trans (add_le_add_right (mul_le_mul_of_nonneg_right (hr i hi) hE) _))
    _ = _ := by simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] <;> ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SingleFormSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-form sieve, with the same actual tilted weights -/

namespace JointDickman

open Finset

theorem single_form_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (θ : ℕ → ℝ) (u v Z : ℕ),
      u ≤ v → 2 ≤ Z → (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 ≤ p) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico u v, ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p)) ≤
        C * ((v : ℝ) - u) * (∏ p ∈ P, (1 - (1 - θ p) / p)) + 2 * (Z + 1 : ℝ) * Z := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_interval_sieve_polynomial hFord hM (by norm_num : 0 < (1 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P θ u v Z huv hZ hP hθ
  have hb := hbound P (fun _ => {0}) θ u v Z huv hZ
    (fun p hp => by simpa using hP p hp) (fun _ _ => by simp) hθ
  have heq (n : ℕ) : (∏ p ∈ rootEvents P (fun _ => {0}) n, θ p) =
      ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) := by
    simp only [rootEvents, prod_filter, mem_singleton, residueWeight]
    congr!
  simp_rw [heq] at hb
  have hfactor (p : ℕ) : 1 - 1 / (p : ℝ) + 1 / p * θ p = 1 - (1 - θ p) / p := by ring
  simpa only [card_singleton, Nat.cast_one, pow_one, hfactor] using hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SingleCoefficientTilt
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential count moments for one actual coefficient -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem single_tilted_density_normalization
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ B Z : ℕ, 1 < B → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      ∀ (Q : Finset ℕ) (s : ℝ), Real.exp s ≤ 2 →
      coefficientScale B * tiltedSieveDensity (auxiliaryCutoff B) Z Q s ≤
      M * Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) := by
  obtain ⟨C, hC, hbound⟩ := coefficient_sieve_density_bound hM hδ
  refine ⟨C * Real.exp 4, by positivity, ?_⟩
  intro B Z hB hPZ hlog Q s hs
  calc
    _ ≤ coefficientScale B * (roughSieveDensity (auxiliaryCutoff B) Z *
        Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q + 4)) :=
      mul_le_mul_of_nonneg_left (tilted_sieve_density_bound _ _ Q hs) (coefficientScale_nonneg B)
    _ = (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) *
        Real.exp 4 * Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := by gcongr; exact hbound B Z hB hPZ hlog

theorem single_coefficient_exp_moment
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z u v : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z → u ≤ v →
      ∀ (Q : Finset ℕ) (s : ℝ), Real.exp s ≤ 2 →
      (∑ n ∈ Ico u v, tiltedCoefficientWeight B Q s n) ≤
      C * ((v : ℝ) - u) * Real.exp (((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
      coefficientScale B * (2 * (Z + 1 : ℝ) * Z) := by
  obtain ⟨Cs, hCs, hsieve⟩ := single_form_interval_sieve hFord hM
  obtain ⟨M, hMpos, hnorm⟩ := single_tilted_density_normalization hM hδ
  refine ⟨Cs * M, mul_pos hCs hMpos, ?_⟩
  intro B Z u v hB hZ hPZ hlog huv Q s hs
  have hP : ∀ p ∈ sievePrimes Z, p.Prime ∧ p ≤ Z ∧ 2 ≤ p := by
    intro p hp
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hpZ).2, (Nat.mem_primesLE.mp hpZ).1, by omega⟩
  have hb := hsieve (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q s) u v Z huv hZ hP
    (fun p _ => tiltedSieveTheta_bounds _ Q hs p)
  have hlen : 0 ≤ (v : ℝ) - u := sub_nonneg.mpr (by exact_mod_cast huv)
  have hmain := mul_le_mul_of_nonneg_left (hnorm B Z hB hPZ hlog Q s hs)
    (mul_nonneg hCs.le hlen)
  calc
    _ ≤ ∑ n ∈ Ico u v, coefficientScale B *
        ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) :=
      sum_le_sum (fun n _ => tiltedCoefficientWeight_le_sieved B Z Q hs n)
    _ = coefficientScale B * (∑ n ∈ Ico u v,
        ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p)) :=
      (mul_sum _ _ _).symm
    _ ≤ coefficientScale B * (Cs * ((v : ℝ) - u) *
        tiltedSieveDensity (auxiliaryCutoff B) Z Q s + 2 * (Z + 1 : ℝ) * Z) :=
      mul_le_mul_of_nonneg_left hb (coefficientScale_nonneg B)
    _ ≤ _ := by
      dsimp only [tiltedSieveDensity] at hmain ⊢
      nlinarith only [hmain]

theorem single_coefficient_count_tail
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z u v : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z → u ≤ v →
      ∀ (Q : Finset ℕ) (s r : ℝ), Real.exp s ≤ 2 →
      (∑ n ∈ Ico u v, if s * r ≤ s * primeDivisorCount Q n then coefficientWeight B n else 0) ≤
      C * ((v : ℝ) - u) * Real.exp (-s * r + ((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
      Real.exp (-s * r) * coefficientScale B * (2 * (Z + 1 : ℝ) * Z) := by
  obtain ⟨C, hC, hbound⟩ := single_coefficient_exp_moment hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B Z u v hB hZ hPZ hlog huv Q s r hs
  have hm := weighted_exp_markov (Ico u v) (coefficientWeight B) (fun n => primeDivisorCount Q n) s r
    (fun n _ => coefficientWeight_nonneg B n)
  have hb := mul_le_mul_of_nonneg_left (hbound B Z u v hB hZ hPZ hlog huv Q s hs)
    (Real.exp_pos (-s * r)).le
  have h := hm.trans hb
  simpa only [tiltedCoefficientWeight, mul_add, Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SingleCoefficientIndicators
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual regularity events for one coefficient -/

namespace JointDickman

open Finset

private theorem indicator_le_of_imp {P Q : Prop} [Decidable P] [Decidable Q] {w : ℝ}
    (hw : 0 ≤ w) (h : P → Q) : (if P then w else 0) ≤ if Q then w else 0 := by
  split_ifs with hp hq hq
  · rfl
  · exact False.elim (hq (h hp))
  · exact hw
  · rfl

open Classical in
theorem single_prefix_upper_indicator {B n : ℕ} (g τ s : ℝ) (hs : 0 < s) :
    (if (g / 2 + τ) * auxiliaryLogLength B < ((primePrefix B g (coefficientPrimeSet B n)).card : ℝ)
      then coefficientWeight B n else 0) ≤
    if s * ((g / 2 + τ) * auxiliaryLogLength B) ≤
      s * primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) n then coefficientWeight B n else 0 := by
  by_cases hn : n = 0
  · simp only [hn, coefficientWeight_zero, ite_self, le_refl]
  · apply indicator_le_of_imp (coefficientWeight_nonneg B n)
    intro h
    rw [← coefficient_prefix_count (B := B) hn g]
    exact mul_le_mul_of_nonneg_left h.le hs.le

open Classical in
theorem single_prefix_lower_indicator {B n : ℕ} (g τ s : ℝ) (hs : 0 < s) :
    (if ((primePrefix B g (coefficientPrimeSet B n)).card : ℝ) < (g / 2 - τ) * auxiliaryLogLength B
      then coefficientWeight B n else 0) ≤
    if (-s) * ((g / 2 - τ) * auxiliaryLogLength B) ≤
      (-s) * primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) n then coefficientWeight B n else 0 := by
  by_cases hn : n = 0
  · simp only [hn, coefficientWeight_zero, ite_self, le_refl]
  · apply indicator_le_of_imp (coefficientWeight_nonneg B n)
    intro h
    rw [← coefficient_prefix_count (B := B) hn g]
    exact mul_le_mul_of_nonpos_left h.le (by linarith only [hs])

open Classical in
theorem single_tail_indicator {B n i : ℕ} (C : ℝ) :
    (if (((coefficientPrimeSet B n).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
      (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then coefficientWeight B n else 0) ≤
    if (-(1 / 10 : ℝ)) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C) ≤
      (-(1 / 10 : ℝ)) * primeDivisorCount
        ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) n
      then coefficientWeight B n else 0 := by
  by_cases hn : n = 0
  · simp only [hn, coefficientWeight_zero, ite_self, le_refl]
  · apply indicator_le_of_imp (coefficientWeight_nonneg B n)
    intro h
    rw [← coefficient_tail_count (B := B) hn (primeTailEndpoint B i)]
    exact mul_le_mul_of_nonpos_left h.le (by norm_num)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingleViolationBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted regularity violations for a single coefficient -/

namespace JointDickman

open Finset

theorem singleCoefficientRemainder_nonneg (B Z : ℕ) : 0 ≤ singleCoefficientRemainder B Z := by
  have hs := coefficientScale_nonneg B
  unfold singleCoefficientRemainder
  positivity

open Classical in
theorem single_prefix_pair_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B u v : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → u ≤ v →
      ∀ (g τ s : ℝ), 0 < s → Real.exp s ≤ 2 → Real.exp (-s) ≤ 2 →
      (∑ n ∈ Ico u v,
        ((if ((primePrefix B g (coefficientPrimeSet B n)).card : ℝ) <
          (g / 2 - τ) * auxiliaryLogLength B then coefficientWeight B n else 0) +
        (if (g / 2 + τ) * auxiliaryLogLength B <
          ((primePrefix B g (coefficientPrimeSet B n)).card : ℝ) then coefficientWeight B n else 0))) ≤
      C * ((v : ℝ) - u) * (prefixLowerFactor B (δ / 8) g τ s + prefixUpperFactor B (δ / 8) g τ s) +
      (Real.exp (s * ((g / 2 - τ) * auxiliaryLogLength B)) +
        Real.exp (-s * ((g / 2 + τ) * auxiliaryLogLength B))) *
          singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
  obtain ⟨C, hC, hb⟩ := single_coefficient_count_tail hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C, hC, ?_⟩
  intro B u v hB hZ hPZ hlog huv g τ s hs he hen
  have hlo := hb B (sieveCutoff (δ / 8) B) u v hB hZ hPZ hlog huv
    (primePrefix B g (auxiliaryPrimes B)) (-s) ((g / 2 - τ) * auxiliaryLogLength B) hen
  have hup := hb B (sieveCutoff (δ / 8) B) u v hB hZ hPZ hlog huv
    (primePrefix B g (auxiliaryPrimes B)) s ((g / 2 + τ) * auxiliaryLogLength B) he
  have hlow := (sum_le_sum (fun n _ => single_prefix_lower_indicator (B := B) (n := n) g τ s hs)).trans hlo
  have hupp := (sum_le_sum (fun n _ => single_prefix_upper_indicator (B := B) (n := n) g τ s hs)).trans hup
  simp only [neg_neg, mul_assoc] at hlow hupp
  rw [sum_add_distrib]
  have h := add_le_add hlow hupp
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [prefixLowerFactor, prefixUpperFactor, singleCoefficientRemainder, mul_assoc]
  ring

open Classical in
theorem single_tail_violation_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B u v : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → u ≤ v →
      ∀ (i : ℕ) (C₀ : ℝ),
      (∑ n ∈ Ico u v, if (((coefficientPrimeSet B n).filter
        (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
          (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀
        then coefficientWeight B n else 0) ≤
      C * ((v : ℝ) - u) * tailChernoffFactor B i (δ / 8) C₀ +
      Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀)) *
        singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
  obtain ⟨C, hC, hb⟩ := single_coefficient_count_tail hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C, hC, ?_⟩
  intro B u v hB hZ hPZ hlog huv i C₀
  have he : Real.exp (-(1 / 10 : ℝ)) ≤ 2 :=
    (Real.exp_le_exp.mpr (by norm_num : -(1 / 10 : ℝ) ≤ 0)).trans (by norm_num)
  have h := hb B (sieveCutoff (δ / 8) B) u v hB hZ hPZ hlog huv
    ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) (-(1 / 10 : ℝ))
    ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀) he
  have hh := (sum_le_sum (fun n _ => single_tail_indicator (B := B) (n := n) (i := i) C₀)).trans h
  simpa only [tailChernoffFactor, singleCoefficientRemainder, neg_neg, mul_assoc] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SingleSieveRemainder
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A power saving in the one-coefficient sieve remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem single_coefficient_remainder_power {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, ∀ H : ℝ, Real.exp (δ * B) ≤ H →
      singleCoefficientRemainder B (sieveCutoff (δ / 8) B) ≤ H / (B : ℝ)^10 := by
  have hlim : Tendsto (fun B : ℕ => 4 * ((B : ℝ)^11 / Real.exp ((3 * δ / 4) * B)))
      atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 11 (by linarith : 0 < 3 * δ / 4)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, mul_zero] using (h.comp tendsto_natCast_atTop_atTop).const_mul 4
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    coefficientScale_eventually_le, sieveCutoff_eventually (by linarith : 0 < δ / 8),
    eventually_gt_atTop 0] with B hsmall hscale hcut hB
  intro H hH
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hF : 1 ≤ Real.exp ((δ / 8) * B) := Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hB0.le)
  have hZ0 : (0 : ℝ) ≤ sieveCutoff (δ / 8) B := Nat.cast_nonneg _
  have hZplus : (sieveCutoff (δ / 8) B + 1 : ℝ) ≤ 2 * Real.exp ((δ / 8) * B) := by
    linarith only [hcut.2.2.2, hF]
  have hbound : singleCoefficientRemainder B (sieveCutoff (δ / 8) B) ≤
      4 * (B : ℝ) * Real.exp ((δ / 4) * B) := by
    calc
      _ ≤ (B : ℝ) * (2 * (2 * Real.exp ((δ / 8) * B)) * Real.exp ((δ / 8) * B)) := by
        unfold singleCoefficientRemainder
        apply mul_le_mul hscale _ (by positivity) hB0.le
        gcongr
        exact hcut.2.2.2
      _ = _ := by
        rw [show (δ / 4) * (B : ℝ) = (δ / 8) * B + (δ / 8) * B by ring, Real.exp_add]
        ring
  have hsmall' : 4 * (B : ℝ)^11 ≤ Real.exp ((3 * δ / 4) * B) := by
    apply (div_le_one (Real.exp_pos _)).mp
    convert hsmall using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have htotal : (4 * (B : ℝ) * Real.exp ((δ / 4) * B)) * (B : ℝ)^10 ≤ Real.exp (δ * B) := by
    calc
      _ = (4 * (B : ℝ)^11) * Real.exp ((δ / 4) * B) := by ring
      _ ≤ Real.exp ((3 * δ / 4) * B) * Real.exp ((δ / 4) * B) :=
        mul_le_mul_of_nonneg_right hsmall' (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (le_div_iff₀ (pow_pos hB0 10)).mpr
  exact ((mul_le_mul_of_nonneg_right hbound (pow_nonneg hB0.le 10)).trans htotal).trans hH

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingleViolationSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite summation of the one-coefficient regularity violations -/

namespace JointDickman

open Finset

theorem single_prefix_sum_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B u v : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → u ≤ v →
      ∀ (L : ℕ) (τ s : ℝ), 0 < L → 0 ≤ τ → 0 < s → s ≤ 1 →
      Real.exp s ≤ 2 → Real.exp (-s) ≤ 2 →
      0 ≤ auxiliaryLogLength B → auxiliaryLogLength B ≤ Real.log B →
      (∑ n ∈ Ico u v, prefixViolationMass B L τ (coefficientPrimeSet B n) (coefficientWeight B n)) ≤
      C * ((v : ℝ) - u) * prefixGridError B L (δ / 8) τ s +
      2 * L * B * singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
  classical
  obtain ⟨C, hC, hbound⟩ := single_prefix_pair_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B u v hB hZ hPZ hlog huv L τ s hL hτ hs hs1 he hen hℓ hℓlog
  unfold prefixViolationMass
  rw [sum_comm]
  have hh := sum_le_linear_remainder (Icc 1 L)
    (fun i => ∑ n ∈ Ico u v,
      ((if ((primePrefix B ((i : ℝ) / L) (coefficientPrimeSet B n)).card : ℝ) <
        (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then coefficientWeight B n else 0) +
      (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
        ((primePrefix B ((i : ℝ) / L) (coefficientPrimeSet B n)).card : ℝ) then coefficientWeight B n else 0)))
    (fun i => prefixLowerFactor B (δ / 8) ((i : ℝ) / L) τ s + prefixUpperFactor B (δ / 8) ((i : ℝ) / L) τ s)
    (fun i => Real.exp (s * ((((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B)) +
      Real.exp (-s * ((((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B)))
    (R := 2 * B) (singleCoefficientRemainder_nonneg _ _)
    (fun i _ => hbound B u v hB hZ hPZ hlog huv ((i : ℝ) / L) τ s hs he hen)
    (fun i hi => by
      have hL' : (0 : ℝ) < L := by exact_mod_cast hL
      have hiL : (i : ℝ) ≤ L := by exact_mod_cast (mem_Icc.mp hi).2
      have hm := prefix_markov_multiplier_bounds (by omega : 1 ≤ B)
        (div_nonneg (Nat.cast_nonneg i) hL'.le) ((div_le_one hL').mpr hiL) hτ hs.le hs1 hℓ hℓlog
      linarith only [hm.1, hm.2])
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [prefixGridError, Nat.card_Icc, Nat.add_sub_cancel]
  ring

theorem single_tail_sum_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B u v : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → u ≤ v →
      1 ≤ Real.log (auxiliaryCutoff B) → ∀ (C₀ : ℝ), 0 ≤ C₀ →
      (∑ n ∈ Ico u v, tailViolationMass B C₀ (coefficientPrimeSet B n) (coefficientWeight B n)) ≤
      C * ((v : ℝ) - u) * (∑ i ∈ activeTailIndices B, tailChernoffFactor B i (δ / 8) C₀) +
      (B : ℝ)^2 * singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
  classical
  obtain ⟨C, hC, hbound⟩ := single_tail_violation_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B u v hB hZ hPZ hlog huv hlogP C₀ hC₀
  simp_rw [tailViolationMass_eq_restricted _ _ hC₀ hlogP]
  rw [sum_comm]
  have hh := sum_le_linear_remainder (activeTailIndices B)
    (fun i => ∑ n ∈ Ico u v,
      if (((coefficientPrimeSet B n).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀ then coefficientWeight B n else 0)
    (fun i => tailChernoffFactor B i (δ / 8) C₀)
    (fun i => Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀)))
    (R := B) (singleCoefficientRemainder_nonneg _ _)
    (fun i _ => hbound B u v hB hZ hPZ hlog huv i C₀)
    (fun i _ => by
      apply tail_markov_multiplier_bound (by exact_mod_cast (by omega : 1 ≤ B)) _ hC₀
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hlogP)
  apply hh.trans
  apply add_le_add_right
  have hcard : ((activeTailIndices B).card : ℝ) ≤ B := by
    exact_mod_cast (calc (activeTailIndices B).card ≤ (range B).card := card_filter_le _ _
                        _ = B := card_range B)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg B))
    (singleCoefficientRemainder_nonneg B (sieveCutoff (δ / 8) B))
  nlinarith only [h]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientRegularityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing mass discarded by the coefficient regularity cutoff -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem regularityRemainder_nonneg (B L : ℕ) : 0 ≤ regularityRemainder B L := by
  unfold regularityRemainder
  positivity

theorem regularityRemainder_tendsto (L : ℕ) :
    Tendsto (fun B => regularityRemainder B L) atTop (𝓝 0) := by
  have h₉ : Tendsto (fun B : ℕ => (2 * (L : ℝ)) / (B : ℝ)^9) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (9 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have h₈ : Tendsto (fun B : ℕ => (1 : ℝ) / (B : ℝ)^8) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (8 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun B : ℕ => (2 * (L : ℝ)) / (B : ℝ)^9 + (1 : ℝ) / (B : ℝ)^8) atTop (𝓝 0) := by
    simpa using h₉.add h₈
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with B hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  unfold regularityRemainder
  field_simp [hB0]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingleRegularityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-weight regularity-loss estimate -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficient_truncation_loss_bound (B L n : ℕ) (τ C : ℝ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) :
    coefficientWeight B n - regularCoefficientWeight B L τ C n ≤
      prefixViolationMass B L τ (coefficientPrimeSet B n) (coefficientWeight B n) +
      tailViolationMass B C (coefficientPrimeSet B n) (coefficientWeight B n) := by
  have hw := coefficientWeight_nonneg B n
  unfold regularCoefficientWeight
  split_ifs with hreg
  · simpa only [sub_self] using add_nonneg
      (prefixViolationMass_nonneg B L τ (coefficientPrimeSet B n) hw)
      (tailViolationMass_nonneg B C (coefficientPrimeSet B n) hw)
  · simpa only [sub_zero] using regularity_failure_union_bound (coefficientPrimeSet B n) hC hlog hw hreg

/-- The first-moment version of manuscript (9), with an error sequence
independent of the interval and the tail cutoff. -/
theorem single_coefficient_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (u v : ℕ), 0 ≤ C → u ≤ v →
          Real.exp (δ * B) ≤ (v : ℝ) - u →
          (∑ n ∈ Ico u v, (coefficientWeight B n - regularCoefficientWeight B L τ C n)) ≤
            K * ((v : ℝ) - u) * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨Cp, hCp, hp⟩ := single_prefix_sum_bound hFord hM hδ
  obtain ⟨Ct, hCt, ht⟩ := single_tail_sum_bound hFord hM hδ
  obtain ⟨D, hD, htail⟩ := actual_tail_chernoff_sum hM (by linarith : 0 < δ / 8)
    (by linarith : δ / 8 ≤ 4)
  let K := Cp + Ct * D + 1
  have hK : 0 < K := by dsimp [K] <;> positivity
  refine ⟨K, hK, ?_⟩
  intro L τ hL hτ
  obtain ⟨s, hs, hs1, he, hen, hprefix⟩ := prefixGridError_tendsto hM hτ
  let ε := fun B => prefixGridError B L (δ / 8) τ s + regularityRemainder B L
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (hprefix L (δ / 8) hL (by linarith) (by linarith)).add (regularityRemainder_tendsto L)
  refine ⟨ε, fun B => add_nonneg (prefixGridError_nonneg ..) (regularityRemainder_nonneg ..), hε, ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8), htail,
    auxiliaryLogLength_between, single_coefficient_remainder_power hδ, hloglarge,
    eventually_gt_atTop 1] with B hcut htailB hℓ hrem hlog hB
  intro C u v hC huv hlen
  let H := (v : ℝ) - u
  let E := singleCoefficientRemainder B (sieveCutoff (δ / 8) B)
  have hH : 0 ≤ H := (Real.exp_pos _).le.trans hlen
  have hpB := hp B u v hB hcut.1 hcut.2.1 (by linarith only [hcut.2.2.1]) huv
    L τ s hL hτ.le hs (by linarith only [hs1]) he hen hℓ.1 hℓ.2
  have htB := ht B u v hB hcut.1 hcut.2.1 (by linarith only [hcut.2.2.1]) huv hlog C hC
  have hmass := sum_le_sum (s := Ico u v) (fun n _ => coefficient_truncation_loss_bound B L n τ C hC hlog)
  rw [sum_add_distrib] at hmass
  have hsum := hmass.trans (add_le_add hpB htB)
  have htail' := mul_le_mul_of_nonneg_left
    (htailB (activeTailIndices B) C (fun i hi => (mem_filter.mp hi).2.le)) (mul_nonneg hCt.le hH)
  have hrem' : (2 * (L : ℝ) * B + (B : ℝ)^2) * E ≤ H * regularityRemainder B L := by
    have hh := mul_le_mul_of_nonneg_left (hrem H hlen)
      (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) * B + (B : ℝ)^2)
    simpa only [E, regularityRemainder, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hCpK : Cp ≤ K := by dsimp [K]; linarith only [mul_pos hCt hD]
  have hCtK : Ct * D ≤ K := by dsimp [K]; linarith only [hCp]
  have h1K : 1 ≤ K := by dsimp [K]; linarith only [hCp, mul_pos hCt hD]
  have hp' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpK hH)
    (prefixGridError_nonneg B L (δ / 8) τ s)
  have ht' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtK hH)
    (Real.exp_pos (-(1 / 10 : ℝ) * C)).le
  have hr' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1K hH)
    (regularityRemainder_nonneg B L)
  change _ ≤ K * H * (ε B + Real.exp (-(1 / 10 : ℝ) * C))
  dsimp only [H, E] at htail' hrem' hp' ht' hr'
  dsimp only [ε, H]
  nlinarith only [hsum, htail', hrem', hp', ht', hr']

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SingleSieveMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-coefficient mean bound from the published upper sieve -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem single_coefficient_mean_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ u v : ℕ, u ≤ v →
      Real.exp (δ * B) ≤ (v : ℝ) - u →
      (∑ n ∈ Ico u v, coefficientWeight B n) ≤ C * ((v : ℝ) - u) := by
  obtain ⟨C, hC, hbound⟩ := single_coefficient_exp_moment hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C + 1, by linarith only [hC], ?_⟩
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8),
    single_coefficient_remainder_power hδ, eventually_gt_atTop 1] with B hcut hrem hB
  intro u v huv hlen
  have hb := hbound B (sieveCutoff (δ / 8) B) u v hB hcut.1 hcut.2.1
    (by linarith only [hcut.2.2.1]) huv ∅ 0 (by norm_num)
  have hm : (∑ n ∈ Ico u v, coefficientWeight B n) ≤ C * ((v : ℝ) - u) +
      singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
    simpa [tiltedCoefficientWeight, singleCoefficientRemainder] using hb
  have hH : 0 ≤ (v : ℝ) - u := (Real.exp_pos _).le.trans hlen
  have hp : (1 : ℝ) ≤ (B : ℝ)^10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ B))
  have he := (hrem _ hlen).trans (div_le_self hH hp)
  nlinarith only [hm, he]

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

theorem coefficient_truncation_loss_nonneg (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    0 ≤ coefficientWeight B n - regularCoefficientWeight B L τ C n :=
  sub_nonneg.mpr (regularCoefficientWeight_le B L τ C n)

theorem independent_truncation_loss_pointwise (B L : ℕ) (τ C : ℝ) (a b : ℕ) :
    coefficientWeight B a * coefficientWeight B b -
        regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C b ≤
      (coefficientWeight B a - regularCoefficientWeight B L τ C a) * coefficientWeight B b +
        coefficientWeight B a * (coefficientWeight B b - regularCoefficientWeight B L τ C b) := by
  have h := mul_nonneg (coefficient_truncation_loss_nonneg B L τ C a)
    (coefficient_truncation_loss_nonneg B L τ C b)
  nlinarith only [h]

theorem independent_truncation_loss_sum (B L : ℕ) (τ C : ℝ) (I J : Finset ℕ) :
    (∑ a ∈ I, ∑ b ∈ J, (coefficientWeight B a * coefficientWeight B b -
        regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C b)) ≤
      (∑ a ∈ I, (coefficientWeight B a - regularCoefficientWeight B L τ C a)) *
        (∑ b ∈ J, coefficientWeight B b) +
      (∑ a ∈ I, coefficientWeight B a) *
        (∑ b ∈ J, (coefficientWeight B b - regularCoefficientWeight B L τ C b)) := by
  calc
    _ ≤ ∑ a ∈ I, ∑ b ∈ J,
        ((coefficientWeight B a - regularCoefficientWeight B L τ C a) * coefficientWeight B b +
          coefficientWeight B a * (coefficientWeight B b - regularCoefficientWeight B L τ C b)) := by
      exact sum_le_sum fun a _ => sum_le_sum fun b _ =>
        independent_truncation_loss_pointwise B L τ C a b
    _ = _ := by
      simp only [sum_add_distrib, sum_mul, mul_sum]
      congr 1 <;> apply sum_comm

/-- The independent two-variable assertion of the manuscript's regularity-loss lemma: the
loss is bounded by the area, uniformly in the tail cutoff. The two inputs
are the cited upper sieve and reciprocal-prime Mertens estimate. -/
theorem independent_coefficient_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (u v x y : ℕ), 0 ≤ C → u ≤ v → x ≤ y →
          Real.exp (δ * B) ≤ (v : ℝ) - u → Real.exp (δ * B) ≤ (y : ℝ) - x →
          (∑ a ∈ Ico u v, ∑ b ∈ Ico x y, (coefficientWeight B a * coefficientWeight B b -
            regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C b)) ≤
            K * ((v : ℝ) - u) * ((y : ℝ) - x) * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hloss⟩ := single_coefficient_regularity_loss hFord hM hδ hδ32
  obtain ⟨M, hM0, hmean⟩ := single_coefficient_mean_bound hFord hM hδ
  refine ⟨2 * K * M, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε0, hε, hlarge⟩ := hloss L τ hL hτ
  refine ⟨ε, hε0, hε, ?_⟩
  filter_upwards [hlarge, hmean] with B hl hm
  intro C u v x y hC huv hxy huvlen hxylen
  have hu := hl C u v hC huv huvlen
  have hx := hl C x y hC hxy hxylen
  have hmu := hm u v huv huvlen
  have hmx := hm x y hxy hxylen
  have hu0 : 0 ≤ ∑ a ∈ Ico u v, coefficientWeight B a :=
    sum_nonneg fun a _ => coefficientWeight_nonneg B a
  have hx0 : 0 ≤ ∑ b ∈ Ico x y, coefficientWeight B b :=
    sum_nonneg fun b _ => coefficientWeight_nonneg B b
  have hdx0 : 0 ≤ ∑ b ∈ Ico x y, (coefficientWeight B b - regularCoefficientWeight B L τ C b) :=
    sum_nonneg fun b _ => coefficient_truncation_loss_nonneg B L τ C b
  have hU : 0 ≤ (v : ℝ) - u := (Real.exp_pos _).le.trans huvlen
  have hX : 0 ≤ (y : ℝ) - x := (Real.exp_pos _).le.trans hxylen
  have hF : 0 ≤ ε B + Real.exp (-(1 / 10 : ℝ) * C) := add_nonneg (hε0 B) (Real.exp_pos _).le
  have h1 := mul_le_mul hu hmx hx0 (mul_nonneg (mul_nonneg hK.le hU) hF)
  have h2 := mul_le_mul hmu hx hdx0 (mul_nonneg hM0.le hU)
  calc
    _ ≤ _ := independent_truncation_loss_sum B L τ C (Ico u v) (Ico x y)
    _ ≤ (K * ((v : ℝ) - u) * (ε B + Real.exp (-(1 / 10 : ℝ) * C))) * (M * ((y : ℝ) - x)) +
        (M * ((v : ℝ) - u)) * (K * ((y : ℝ) - x) * (ε B + Real.exp (-(1 / 10 : ℝ) * C))) :=
      add_le_add h1 h2
    _ = _ := by ring

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

theorem bernoulliSubsetMass_eq_uncorrected_odds {P S : Finset ℕ} (q : ℕ → ℝ)
    (hS : S ⊆ P) (hq : ∀ p ∈ S, 1 - q p ≠ 0) :
    bernoulliSubsetMass P q S =
      uncorrectedSubsetMass P q S * ∏ p ∈ S, (1 - q p)⁻¹ := by
  rw [uncorrectedSubsetMass_identity q hS, prod_inv_distrib, mul_assoc,
    mul_inv_cancel₀ (prod_ne_zero_iff.mpr hq), mul_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryOdds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded odds corrections at the manuscript's auxiliary scale -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_mul_sqrt_ratio {B : ℕ} (hB : 1 < B) :
    coefficientScale B * auxiliaryRatio B ^ (1 / 2 : ℝ) = B := by
  unfold coefficientScale
  rw [mul_assoc, ← Real.rpow_add (auxiliaryRatio_pos hB)]
  norm_num only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [mul_comm, auxiliaryRatio_mul_log hB]

theorem primeNormalizer_coefficientScale_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      primeNormalizer (auxiliaryPrimes B) (1 / 2) ≤ C * coefficientScale B / B := by
  let C : ℝ := (4 : ℝ) ^ (-(1 / 2 : ℝ)) + 1
  have hC : 0 < C := by unfold C; positivity
  refine ⟨C, hC, ?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1 / 2) (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (Iio_mem_nhds (show (4 : ℝ) ^ (-(1 / 2 : ℝ)) < C by
      dsimp [C] <;> linarith)), eventually_gt_atTop 1] with B hQ hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  apply (le_div_iff₀ hB0).mpr
  calc
    _ = (primeNormalizer (auxiliaryPrimes B) (1 / 2) * auxiliaryRatio B ^ (1 / 2 : ℝ)) *
        coefficientScale B := by rw [mul_right_comm, mul_assoc, coefficientScale_mul_sqrt_ratio hB]
    _ ≤ C * coefficientScale B :=
      mul_le_mul_of_nonneg_right hQ.le (coefficientScale_nonneg B)

theorem auxiliary_selected_odds_bound :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
      (∏ p ∈ S, (1 - (1 / 2 : ℝ) / p)⁻¹) ≤ Real.exp 1 := by
  have ht : Tendsto (fun B : ℕ => (32 / (5 * Real.log 2)) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have hp := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (32 / (5 * Real.log 2))
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using hp
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp (hS hp)).1).2
  have hcut : ∀ p ∈ S, (auxiliaryCutoff B : ℝ) ≤ p := by
    intro p hp
    exact (mem_filter.mp (hS hp)).2.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ (16 / 5 : ℝ) * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  apply (inverseSelectedPrimeOdds_le hP (by norm_num) (by norm_num) S hprime hcut).trans
  apply Real.exp_le_exp.mpr
  calc
    2 * (S.card : ℝ) / auxiliaryCutoff B ≤
        2 * ((16 / 5 : ℝ) * B / Real.log 2) / auxiliaryCutoff B := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hP.le
    _ = (32 / (5 * Real.log 2)) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
    _ ≤ 1 := hsmall.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDomination
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Manuscript equation (4): domination by the coefficient weight -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The actual prime-product probability is bounded by A₀(n)/(Bn),
uniformly over the full product range needed by the application. -/
theorem primeProductMass_coefficient_domination
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ n : ℕ, 0 < n →
      (n : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
      primeProductMass (auxiliaryPrimes B) (1 / 2) n ≤
        C * coefficientWeight B n / ((B : ℝ) * n) := by
  obtain ⟨C, hC, hQ⟩ := primeNormalizer_coefficientScale_bound hM
  refine ⟨Real.exp 1 * C, mul_pos (Real.exp_pos _) hC, ?_⟩
  filter_upwards [hQ, auxiliary_selected_odds_bound, eventually_gt_atTop 1] with B hQB hodds hB
  intro n hn hsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 ≤ roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n := by
    unfold roughSquarefreeWeight squarefreeWeight
    simp only [ArithmeticFunction.coe_mk]
    split_ifs <;> positivity
  by_cases hs : n ∈ (auxiliaryPrimes B).powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hs
    have hS : S ⊆ auxiliaryPrimes B := mem_powerset.mp hSP
    have hprime : ∀ p ∈ auxiliaryPrimes B, p.Prime := by
      intro p hp
      exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
    have hnonzero : ∀ p ∈ S, 1 - (1 / 2 : ℝ) / p ≠ 0 := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p (hS hp)).two_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hf : (1 / 2 : ℝ) / p < 1 := (div_lt_one hp0).mpr (by linarith)
      linarith
    have hmass : primeProductMass (auxiliaryPrimes B) (1 / 2) n =
        uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S *
          ∏ p ∈ S, (1 - (1 / 2 : ℝ) / p)⁻¹ := by
      rw [← hSn, primeProductMass_at_product (1 / 2) hprime hS,
        bernoulliSubsetMass_eq_uncorrected_odds _ hS hnonzero]
    have hnU : (n : ℝ) ≤ auxiliaryUpper B := by
      refine hsize.trans (Real.exp_le_exp.mpr ?_)
      nlinarith
    have hunc : uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S =
        primeNormalizer (auxiliaryPrimes B) (1 / 2) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n := by
      rw [← uncorrectedPrimeProductMass_at_product (1 / 2) hprime hS, hSn]
      exact uncorrectedPrimeProductMass_harmonic hnU (1 / 2)
    have hunc0 : 0 ≤ uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S := by
      unfold uncorrectedSubsetMass
      apply mul_nonneg
      · apply prod_nonneg
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
        have hf : (1 / 2 : ℝ) / p ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)
        linarith
      · exact prod_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))
    rw [hmass]
    calc
      _ ≤ uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (hodds S hS (by simpa only [hSn] using hsize)) hunc0
      _ = Real.exp 1 * primeNormalizer (auxiliaryPrimes B) (1 / 2) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n := by rw [hunc]; ring
      _ ≤ Real.exp 1 * (C * coefficientScale B / B) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQB (Real.exp_pos _).le) hr) hn0.le
      _ = _ := by unfold coefficientWeight; ring
  · rw [primeProductMass_eq_zero (1 / 2) n hs]
    exact div_nonneg (mul_nonneg (mul_pos (Real.exp_pos _) hC).le (coefficientWeight_nonneg B n))
      (mul_nonneg hB0.le hn0.le)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientProbabilityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic probability bounds for nonregular coefficient pairs -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryHalfMass_nonneg (B n : ℕ) :
    0 ≤ primeProductMass (auxiliaryPrimes B) (1 / 2) n := by
  classical
  unfold primeProductMass
  apply sum_nonneg
  intro S hS
  split_ifs
  · apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.two_le
    exact ⟨div_nonneg (by norm_num) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith)⟩
  · exact le_rfl

theorem coefficientPairFailureMass_nonneg (B L : ℕ) (τ C : ℝ) (a c : ℕ) :
    0 ≤ coefficientPairFailureMass B L τ C a c := by
  unfold coefficientPairFailureMass
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (auxiliaryHalfMass_nonneg B a) (auxiliaryHalfMass_nonneg B c)

theorem coefficientPairFailureMass_le {B L a c : ℕ} {τ C D : ℝ}
    (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hma : primeProductMass (auxiliaryPrimes B) (1 / 2) a ≤
      D * coefficientWeight B a / ((B : ℝ) * a))
    (hmc : primeProductMass (auxiliaryPrimes B) (1 / 2) c ≤
      D * coefficientWeight B c / ((B : ℝ) * c)) (hD : 0 ≤ D) :
    coefficientPairFailureMass B L τ C a c ≤
      D^2 / ((B : ℝ)^2 * a * c) *
        (coefficientWeight B a * coefficientWeight B c -
          regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C c) := by
  classical
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  by_cases hreg : RegularPrimeSet B L τ C (coefficientPrimeSet B a) ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B c)
  · simp only [coefficientPairFailureMass, ite_eq_left hreg, regularCoefficientWeight,
      ite_eq_left hreg.1, ite_eq_left hreg.2, sub_self, mul_zero, le_refl]
  · have hzero : regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C c = 0 := by
      unfold regularCoefficientWeight
      split_ifs with ha hc
      · exact False.elim (hreg ⟨ha, hc⟩)
      all_goals ring
    rw [coefficientPairFailureMass, ite_eq_right hreg, hzero, sub_zero]
    calc
      _ ≤ (D * coefficientWeight B a / ((B : ℝ) * a)) *
          (D * coefficientWeight B c / ((B : ℝ) * c)) :=
        mul_le_mul hma hmc (auxiliaryHalfMass_nonneg B c)
          (div_nonneg (mul_nonneg hD (coefficientWeight_nonneg B a)) (mul_nonneg hB0.le ha0.le))
      _ = _ := by field_simp

theorem coefficient_pair_loss_nonneg (B L : ℕ) (τ C : ℝ) (a c : ℕ) :
    0 ≤ coefficientWeight B a * coefficientWeight B c -
      regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C c := by
  exact sub_nonneg.mpr (mul_le_mul (regularCoefficientWeight_le B L τ C a)
    (regularCoefficientWeight_le B L τ C c) (regularCoefficientWeight_nonneg B L τ C c)
    (coefficientWeight_nonneg B a))

/-- The probability loss in one size-and-ratio box is O(B⁻²), with the
same vanishing and tail-cutoff errors as the arithmetic regularity bound. -/
theorem coefficient_failure_box_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T X : ℕ), 0 ≤ C → 0 < T →
          Real.exp (δ * B) ≤ X →
          (4 * T * X : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
          (∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
            coefficientPairFailureMass B L τ C a c) ≤
            K / (B : ℝ)^2 * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨D, hD, hdom⟩ := primeProductMass_coefficient_domination hM
  obtain ⟨K, hK, hloss⟩ := independent_coefficient_regularity_loss hFord hM hδ hδ32
  refine ⟨3 * D^2 * K, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε0, hε, hlarge⟩ := hloss L τ hL hτ
  refine ⟨ε, hε0, hε, ?_⟩
  filter_upwards [hlarge, hdom, eventually_gt_atTop 0] with B hl hd hB
  intro C T X hC hT hX hsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hX0 : (0 : ℝ) < X := (Real.exp_pos _).trans_le hX
  have hXnat : 0 < X := by exact_mod_cast hX0
  have hlen : Real.exp (δ * B) ≤ ((4 * T * X : ℕ) : ℝ) - (T * X : ℕ) := by
    push_cast
    nlinarith only [hX, mul_le_mul_of_nonneg_right hT1 hX0.le]
  have hsum := hl C (T * X) (4 * T * X) X (2 * X) hC (by nlinarith) (by omega)
    hlen (by push_cast; linarith only [hX])
  let E := ε B + Real.exp (-(1 / 10 : ℝ) * C)
  have hprob : (∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
      coefficientPairFailureMass B L τ C a c) ≤
      D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
          (coefficientWeight B a * coefficientWeight B c -
            regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C c)) := by
    simp only [mul_sum]
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro c hc
    have ha' := mem_Ico.mp ha
    have hc' := mem_Ico.mp hc
    have ha0 : 0 < a := lt_of_lt_of_le (Nat.mul_pos hT hXnat) ha'.1
    have hc0 : 0 < c := hXnat.trans_le hc'.1
    have hasize : (a : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) :=
      (by exact_mod_cast ha'.2.le : (a : ℝ) ≤ (4 * T * X : ℝ)).trans hsize
    have hcsize : (c : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
      have hh : (c : ℝ) ≤ 2 * X := by exact_mod_cast hc'.2.le
      exact hh.trans ((by nlinarith only [mul_le_mul_of_nonneg_right hT1 hX0.le] :
        (2 * X : ℝ) ≤ 4 * T * X).trans hsize)
    apply (coefficientPairFailureMass_le hB ha0 hc0 (hd a ha0 hasize) (hd c hc0 hcsize) hD.le).trans
    apply mul_le_mul_of_nonneg_right _ (coefficient_pair_loss_nonneg B L τ C a c)
    apply div_le_div_of_nonneg_left (sq_nonneg D) (by positivity)
    have haR : (T * X : ℝ) ≤ a := by exact_mod_cast ha'.1
    have hcR : (X : ℝ) ≤ c := by exact_mod_cast hc'.1
    gcongr
  calc
    _ ≤ _ := hprob
    _ ≤ D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (K * (((4 * T * X : ℕ) : ℝ) - (T * X : ℕ)) * (((2 * X : ℕ) : ℝ) - X) * E) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      dsimp only [E]
      push_cast
      field_simp
      ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientCutoffRemoval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing coefficient regularity in the normalized amplification mass -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- The actual coefficient-support probability of a failed regularity
cutoff, including the outside B normalization in manuscript (13). -/
theorem coefficient_cutoff_removal
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), 0 ≤ C → 0 < T →
          (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
          (B : ℝ) * (∑ ac ∈ amplificationCoefficientPairs B T,
            coefficientPairFailureMass B L τ C ac.1 ac.2) ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  classical
  obtain ⟨K, hK, hboxes⟩ := coefficient_failure_box_bound hFord hM
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 32)
  refine ⟨4 * K, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε0, hε, hlarge⟩ := hboxes L τ hL hτ
  refine ⟨ε, hε0, hε, ?_⟩
  filter_upwards [hlarge, coefficientDyadicBox_scales, eventually_gt_atTop 0] with B hb hs hB
  intro C T hC hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let F := ε B + Real.exp (-(1 / 10 : ℝ) * C)
  have hF : 0 ≤ F := add_nonneg (hε0 B) (Real.exp_pos _).le
  have hpoint : ∀ k ∈ Ico B (4 * B),
      (∑ ac ∈ coefficientDyadicBox T k, coefficientPairFailureMass B L τ C ac.1 ac.2) ≤
        K / (B : ℝ)^2 * F := by
    intro k hk
    have hscale := hs T k hTsize hk
    unfold coefficientDyadicBox
    rw [sum_product]
    exact hb C T (2^k) hC hT hscale.1 hscale.2
  have hsum : (∑ ac ∈ amplificationCoefficientPairs B T,
      coefficientPairFailureMass B L τ C ac.1 ac.2) ≤
      ((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2 * F) := by
    calc
      _ ≤ ∑ ac ∈ coefficientDyadicCover B T, coefficientPairFailureMass B L τ C ac.1 ac.2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun ac _ _ => coefficientPairFailureMass_nonneg B L τ C ac.1 ac.2)
      _ = ∑ k ∈ Ico B (4 * B), ∑ ac ∈ coefficientDyadicBox T k,
          coefficientPairFailureMass B L τ C ac.1 ac.2 := by
        apply sum_biUnion
        intro k _ l _ hkl
        exact coefficientDyadicBox_disjoint T hkl
      _ ≤ ∑ _k ∈ Ico B (4 * B), K / (B : ℝ)^2 * F := sum_le_sum hpoint
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hcard : ((Ico B (4 * B)).card : ℝ) ≤ 4 * B := by
    exact_mod_cast (show (Ico B (4 * B)).card ≤ 4 * B by rw [Nat.card_Ico]; omega)
  calc
    _ ≤ (B : ℝ) * (((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2 * F)) :=
      mul_le_mul_of_nonneg_left hsum hB0.le
    _ ≤ (B : ℝ) * ((4 * B) * (K / (B : ℝ)^2 * F)) := by
      gcongr
    _ = _ := by
      dsimp only [F]
      field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientEventBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The size-and-ratio event has probability O(1/B) -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryHalfMass_pair_le {B a c : ℕ} {D : ℝ}
    (hB : 0 < B) (ha : 0 < a) (hc : 0 < c) (hD : 0 ≤ D)
    (hma : primeProductMass (auxiliaryPrimes B) (1 / 2) a ≤
      D * coefficientWeight B a / ((B : ℝ) * a))
    (hmc : primeProductMass (auxiliaryPrimes B) (1 / 2) c ≤
      D * coefficientWeight B c / ((B : ℝ) * c)) :
    primeProductMass (auxiliaryPrimes B) (1 / 2) a *
      primeProductMass (auxiliaryPrimes B) (1 / 2) c ≤
      D^2 / ((B : ℝ)^2 * a * c) * (coefficientWeight B a * coefficientWeight B c) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  calc
    _ ≤ (D * coefficientWeight B a / ((B : ℝ) * a)) *
        (D * coefficientWeight B c / ((B : ℝ) * c)) :=
      mul_le_mul hma hmc (auxiliaryHalfMass_nonneg B c)
        (div_nonneg (mul_nonneg hD (coefficientWeight_nonneg B a)) (mul_nonneg hB0.le ha0.le))
    _ = _ := by field_simp

theorem coefficient_pair_box_mass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T k : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) → k ∈ Ico B (4 * B) →
      (∑ ac ∈ coefficientDyadicBox T k,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ K / (B : ℝ)^2 := by
  obtain ⟨D, hD, hdom⟩ := primeProductMass_coefficient_domination hM
  obtain ⟨M, hM0, hmean⟩ := single_coefficient_mean_bound hFord hM (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨3 * D^2 * M^2, by positivity, ?_⟩
  filter_upwards [hdom, hmean, coefficientDyadicBox_scales, eventually_gt_atTop 0]
    with B hd hm hs hB
  intro T k hT hTsize hk
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let X := 2^k
  have hXnat : 0 < X := pow_pos (by norm_num) _
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hXnat
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hscale := hs T k hTsize hk
  have hlen : Real.exp ((1 / 2 : ℝ) * B) ≤ ((4 * T * X : ℕ) : ℝ) - (T * X : ℕ) := by
    push_cast
    nlinarith only [hscale.1, mul_le_mul_of_nonneg_right hT1 hX0.le]
  have hma := hm (T * X) (4 * T * X) (by nlinarith) hlen
  have hmc := hm X (2 * X) (by omega) (by push_cast; linarith only [hscale.1])
  have hcmean : 0 ≤ ∑ c ∈ Ico X (2 * X), coefficientWeight B c :=
    sum_nonneg fun c _ => coefficientWeight_nonneg B c
  have hprod := mul_le_mul hma hmc hcmean
    (mul_nonneg hM0.le (sub_nonneg.mpr (by exact_mod_cast (show T * X ≤ 4 * T * X by nlinarith))))
  have hpair : (∑ ac ∈ coefficientDyadicBox T k,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤
      D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (∑ a ∈ Ico (T * X) (4 * T * X), coefficientWeight B a) *
        (∑ c ∈ Ico X (2 * X), coefficientWeight B c) := by
    unfold coefficientDyadicBox
    rw [sum_product]
    have hfactor : D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (∑ a ∈ Ico (T * X) (4 * T * X), coefficientWeight B a) *
        (∑ c ∈ Ico X (2 * X), coefficientWeight B c) =
        ∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
          D^2 / ((B : ℝ)^2 * (T * X) * X) * (coefficientWeight B a * coefficientWeight B c) := by
      simp only [mul_sum, sum_mul, mul_assoc]
      exact sum_comm
    rw [hfactor]
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro c hc
    have ha' := mem_Ico.mp ha
    have hc' := mem_Ico.mp hc
    have ha0 : 0 < a := lt_of_lt_of_le (Nat.mul_pos hT hXnat) ha'.1
    have hc0 : 0 < c := hXnat.trans_le hc'.1
    have hasize : (a : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) :=
      (by exact_mod_cast ha'.2.le : (a : ℝ) ≤ (4 * T * X : ℝ)).trans hscale.2
    have hcsize : (c : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
      have hh : (c : ℝ) ≤ 2 * X := by exact_mod_cast hc'.2.le
      exact hh.trans ((by nlinarith only [mul_le_mul_of_nonneg_right hT1 hX0.le] :
        (2 * X : ℝ) ≤ 4 * T * X).trans hscale.2)
    apply (auxiliaryHalfMass_pair_le hB ha0 hc0 hD.le (hd a ha0 hasize) (hd c hc0 hcsize)).trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (coefficientWeight_nonneg B a) (coefficientWeight_nonneg B c))
    apply div_le_div_of_nonneg_left (sq_nonneg D) (by positivity)
    have haR : (T * X : ℝ) ≤ a := by exact_mod_cast ha'.1
    have hcR : (X : ℝ) ≤ c := by exact_mod_cast hc'.1
    gcongr
  calc
    _ ≤ _ := hpair
    _ ≤ D^2 / ((B : ℝ)^2 * (T * X) * X) *
        ((M * (((4 * T * X : ℕ) : ℝ) - (T * X : ℕ))) *
          (M * (((2 * X : ℕ) : ℝ) - X))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by
      push_cast
      field_simp
      ring

theorem coefficient_size_ratio_event_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (B : ℝ) * (∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ K := by
  obtain ⟨K, hK, hbound⟩ := coefficient_pair_box_mass_bound hFord hM
  refine ⟨4 * K, by positivity, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hb hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hsum : (∑ ac ∈ amplificationCoefficientPairs B T,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤
      ((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2) := by
    calc
      _ ≤ ∑ ac ∈ coefficientDyadicCover B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun ac _ _ => mul_nonneg (auxiliaryHalfMass_nonneg B ac.1) (auxiliaryHalfMass_nonneg B ac.2))
      _ = ∑ k ∈ Ico B (4 * B), ∑ ac ∈ coefficientDyadicBox T k,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 := by
        apply sum_biUnion
        intro k _ l _ hkl
        exact coefficientDyadicBox_disjoint T hkl
      _ ≤ ∑ _k ∈ Ico B (4 * B), K / (B : ℝ)^2 :=
        sum_le_sum fun k hk => hb T k hT hTsize hk
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hcard : ((Ico B (4 * B)).card : ℝ) ≤ 4 * B := by
    exact_mod_cast (show (Ico B (4 * B)).card ≤ 4 * B by rw [Nat.card_Ico]; omega)
  calc
    _ ≤ (B : ℝ) * (((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hsum hB0.le
    _ ≤ (B : ℝ) * ((4 * B) * (K / (B : ℝ)^2)) := by gcongr
    _ = _ := by field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SelectedCoefficientRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity and integer products of selected prime sets -/

namespace JointDickman

open Finset

theorem coefficientPrimeSet_at_product {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    coefficientPrimeSet B (∏ p ∈ A, p) = A := by
  have hprime : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  have hnonzero : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hprime p hp).ne_zero
  have hpf := Nat.primeFactors_prod hprime
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hpd⟩ := mem_filter.mp hp
    have hh := Nat.mem_primeFactors.mpr ⟨auxiliaryPrimes_prime B p hpP, hpd, hnonzero⟩
    rwa [hpf] at hh
  · intro hp
    have hh : p ∈ (∏ p ∈ A, p).primeFactors := by rwa [hpf]
    exact mem_filter.mpr ⟨hA hp, (Nat.mem_primeFactors.mp hh).2.1⟩

open Classical in
theorem coefficientPairFailureMass_selected_sum (B L T : ℕ) (τ C : ℝ) :
    (∑ ac ∈ amplificationCoefficientPairs B T, coefficientPairFailureMass B L τ C ac.1 ac.2) =
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
          if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D then 0 else
            bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D
        else 0 := by
  let f : ℕ × ℕ → ℝ := fun ac =>
    if RegularPrimeSet B L τ C (coefficientPrimeSet B ac.1) ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B ac.2) then 0 else 1
  have h := primeProductPair_weighted_sum (auxiliaryPrimes B) (1 / 2)
    (amplificationCoefficientPairs B T) f
  have heq : (∑ ac ∈ amplificationCoefficientPairs B T, coefficientPairFailureMass B L τ C ac.1 ac.2) =
      ∑ ac ∈ amplificationCoefficientPairs B T,
        f ac * (primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) := by
    apply sum_congr rfl
    intro ac _
    dsimp [coefficientPairFailureMass, f]
    split_ifs <;> simp only [zero_mul, one_mul]
  rw [heq, h]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  dsimp only [f]
  rw [coefficientPrimeSet_at_product (mem_powerset.mp hA),
    coefficientPrimeSet_at_product (mem_powerset.mp hD)]
  split_ifs <;> simp only [zero_mul, one_mul]

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FourSubsetFailure
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite decomposition of the four regularity failures -/

namespace JointDickman

open Finset

theorem fairRemainingPairFailure_nonneg (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    0 ≤ fairRemainingPairFailure B L τ C A D := by
  unfold fairRemainingPairFailure
  apply sum_nonneg
  intro R hR
  apply sum_nonneg
  intro Q hQ
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hA (mem_powerset.mp hR))
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hD (mem_powerset.mp hQ))

open Classical in
theorem fairFourSubsetFailureAt_union (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    fairFourSubsetFailureAt B L τ C A D ≤
      (if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D then 0 else
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D) +
      fairRemainingPairFailure B L τ C A D := by
  by_cases hreg : RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D
  · simp only [fairFourSubsetFailureAt, hreg, true_and, ite_true, if_true, zero_add, fairRemainingPairFailure]
    exact le_rfl
  · simp only [fairFourSubsetFailureAt, hreg, false_and, ite_false, if_false]
    rw [← sum_mul_sum, fairSelectedRemainingMass_sum (auxiliaryPrimes_prime B) hA,
      fairSelectedRemainingMass_sum (auxiliaryPrimes_prime B) hD]
    exact le_add_of_nonneg_right (fairRemainingPairFailure_nonneg B L τ C hA hD)

open Classical in
theorem fairFourSubsetFailure_union (B L T : ℕ) (τ C : ℝ) :
    fairFourSubsetFailure B L T τ C ≤
      (∑ ac ∈ amplificationCoefficientPairs B T, coefficientPairFailureMass B L τ C ac.1 ac.2) +
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
          fairRemainingPairFailure B L τ C A D else 0 := by
  rw [coefficientPairFailureMass_selected_sum]
  simp only [← sum_add_distrib]
  unfold fairFourSubsetFailure
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  by_cases hmem : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T
  · simp only [hmem, ite_true, if_true]
    exact fairFourSubsetFailureAt_union B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)
  · simp only [hmem, ite_false, if_false, add_zero, le_refl]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing all four regularity cutoffs in the amplification mass -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- In the actual independent-site fair-split model, the B-normalized
size-and-ratio mass lost at any of the four cutoffs tends to zero, up to
the uniform exponential tail-cutoff error. -/
theorem amplification_regularity_loss_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), 0 ≤ C → 0 < T →
          (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
          (B : ℝ) * fairFourSubsetFailure B L T τ C ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  classical
  obtain ⟨Kc, hKc, hcoef⟩ := coefficient_cutoff_removal hFord hM
  obtain ⟨Kr, hKr, hremaining⟩ := fair_remaining_pair_regularity_loss hM
    (by norm_num : (0 : ℝ) < 16 / 5)
  obtain ⟨M, hM0, hmass⟩ := coefficient_size_ratio_event_bound hFord hM
  let K := Kc + M * Kr
  refine ⟨K, by dsimp [K] <;> positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨εc, hεc0, hεc, hclarge⟩ := hcoef L τ hL hτ
  obtain ⟨εr, hεr0, hεr, hrlarge⟩ := hremaining L τ hL hτ
  let ε := fun B => εc B + εr B
  refine ⟨ε, fun B => add_nonneg (hεc0 B) (hεr0 B), ?_, ?_⟩
  · simpa only [ε, add_zero] using hεc.add hεr
  filter_upwards [hclarge, hrlarge, hmass, amplificationCoefficientPairs_size,
    eventually_gt_atTop 0] with B hc hr hm hsize hB
  intro C T hC hT hTsize
  let F := εr B + Real.exp (-(1 / 10 : ℝ) * C)
  have hF : 0 ≤ F := add_nonneg (hεr0 B) (Real.exp_pos _).le
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hrem : (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
        fairRemainingPairFailure B L τ C A D else 0) ≤
      (∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) * Kr * F := by
    rw [primeProductPair_sum_event]
    simp only [sum_mul]
    apply sum_le_sum
    intro A hA
    apply sum_le_sum
    intro D hD
    by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T
    · simp only [hp, ite_true, if_true]
      obtain ⟨ha, hd⟩ := hsize T _ _ hT hTsize hp
      exact hr A D C hC (mem_powerset.mp hA) (mem_powerset.mp hD) ha hd
    · simp only [hp, ite_false, if_false, zero_mul, le_refl]
  have hrem' : (B : ℝ) * (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
        fairRemainingPairFailure B L τ C A D else 0) ≤ M * Kr * F := by
    calc
      _ ≤ (B : ℝ) * ((∑ ac ∈ amplificationCoefficientPairs B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) * Kr * F) :=
        mul_le_mul_of_nonneg_left hrem hB0
      _ = ((B : ℝ) * (∑ ac ∈ amplificationCoefficientPairs B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2)) * Kr * F := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hm T hT hTsize) hKr.le) hF
  have hc' := hc C T hC hT hTsize
  have hu := mul_le_mul_of_nonneg_left (fairFourSubsetFailure_union B L T τ C) hB0
  have hx := mul_nonneg hKc.le (hεr0 B)
  have hy := mul_nonneg (mul_nonneg hM0.le hKr.le) (hεc0 B)
  dsimp only [K, ε, F] at *
  nlinarith only [hu, hc', hrem', hx, hy]

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.amplification_regularity_loss_jd_oai := @OAI.JointDickman.amplification_regularity_loss_jd_oai
