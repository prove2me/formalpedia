-- Prove2me | solution 1 for OAI.GaussianPropeller.Taylor.integral_exp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:32:26.335909+00:00
-- url     : https://prove2.me/submissions/f0980ba4-ddba-485b-a301-b533ba0d786a

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Taylor.lean:L105-L119
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Taylor.integral_exp_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Theorems.Thm_OAI_GaussianPropeller_Taylor_exp_remainder

-- ---- from OAI.Probability.GaussianPropeller.Taylor ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.Taylor
lemma E_zero (n : ℕ) : E n 0 = 1 := by
  unfold E
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp

lemma exp_le_E_even (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ E (2*n) x := by
  obtain rfl | hp := hx.eq_or_lt
  · simp [E_zero]
  obtain ⟨c,h⟩ := exp_remainder hp (2*n)
  have hn : (-1:ℝ)^(2*n+1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [hn] at h
  have : (-1:ℝ)*Real.exp (-c)*x^(2*n+1)/(Nat.factorial (2*n+1)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.exp_pos (-c)]) (pow_nonneg hx _)
    · positivity
  linarith only [h,this]

lemma E_odd_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : E (2*n+1) x ≤ Real.exp (-x) := by
  obtain rfl | hp := hx.eq_or_lt
  · simp [E_zero]
  obtain ⟨c,h⟩ := exp_remainder hp (2*n+1)
  have hn : (-1:ℝ)^(2*n+1+1) = 1 := by rw [show 2*n+1+1=2*(n+1) by omega, pow_mul]; norm_num
  rw [hn] at h
  have : 0 ≤ (1:ℝ)*Real.exp (-c)*x^(2*n+1+1)/(Nat.factorial (2*n+1+1)) := by positivity
  linarith only [h,this]

lemma hasDerivAt_J (n : ℕ) (x : ℝ) : HasDerivAt (J n) (E n (x^2/2)) x := by
  unfold J E
  convert! HasDerivAt.sum (u := Finset.range (n+1)) (fun k hk =>
    (((hasDerivAt_pow (2*k+1) x).const_mul ((-1:ℝ)^k)).div_const
      ((2:ℝ)^k*(Nat.factorial k)*(2*k+1)))) using 1
  · funext y
    simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro k hk
    have hfact : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have hk' : (2*(k:ℝ)+1) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [div_pow, pow_mul]
    field_simp

lemma J_zero (n : ℕ) : J n 0 = 0 := by simp [J]

lemma integral_E (n : ℕ) (x : ℝ) :
    ∫ t in (0:ℝ)..x, E n (t^2/2) = J n x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_J n t)
    (show IntervalIntegrable (fun t : ℝ => E n (t^2/2)) volume 0 x from
      (by unfold E; exact (by fun_prop : Continuous _).intervalIntegrable _ _))
  simpa only [J_zero, sub_zero] using h

lemma integral_exp_bounds (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    J (2*n+1) x ≤ (∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) ∧
      (∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) ≤ J (2*n) x := by
  have hi (k : ℕ) : IntervalIntegrable (fun t : ℝ => E k (t^2/2)) volume 0 x := by
    unfold E; exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have he : IntervalIntegrable (fun t : ℝ => Real.exp (-t^2/2)) volume 0 x := (by fun_prop : Continuous _).intervalIntegrable _ _
  constructor
  · rw [← integral_E]
    apply intervalIntegral.integral_mono_on hx (hi _) he
    intro t ht
    simpa only [neg_div] using E_odd_le_exp n (show (0:ℝ) ≤ t^2/2 by positivity)
  · rw [← integral_E]
    apply intervalIntegral.integral_mono_on hx he (hi _)
    intro t ht
    simpa only [neg_div] using exp_le_E_even n (show (0:ℝ) ≤ t^2/2 by positivity)
end GaussianPropeller.Taylor

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Taylor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Taylor.integral_exp_bounds := @_root_.OAI.GaussianPropeller.Taylor.integral_exp_bounds
