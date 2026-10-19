-- Prove2me | solution 1 for OAI.RepeatedLocalization.log_sum_inequality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:26:02.294473+00:00
-- url     : https://prove2.me/submissions/165a2044-0626-41ca-90f3-12c82b26caef

import Mathlib
import Definitions.Def_OAIQWRLC000

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma xlog_zero : xlog 0 = 0 := by simp [xlog]

lemma xlog_lower_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    xlog y + (Real.log y+1)*(x-y) ≤ xlog x := by
  have h := Real.self_sub_one_le_mul_log (div_nonneg hx hy.le)
  by_cases hx0 : x = 0
  · simp only [hx0, xlog]
    nlinarith
  rw [Real.log_div hx0 hy.ne'] at h
  have H := mul_le_mul_of_nonneg_left h hy.le
  dsimp [xlog]
  field_simp at H
  nlinarith

lemma log_ratio_lower {a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : 0 < P) (hz : b = 0 → a = 0) :
    a*(Real.log P+1)-P*b ≤ a*Real.log (a/b) := by
  by_cases hb0 : b = 0
  · simp [hb0,hz hb0]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have h := xlog_lower_tangent (div_nonneg ha hb) hP
  have H := mul_le_mul_of_nonneg_left h hb
  dsimp [xlog] at H
  field_simp at H
  nlinarith

lemma log_sum_inequality_oai {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hb1 : ∑ i, b i = 1)
    (hz : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log (∑ i, a i) ≤ ∑ i, a i * Real.log (a i / b i) := by
  show xlog (∑ i,a i) ≤ ∑ i,a i * Real.log (a i/b i)
  have hA : 0 ≤ ∑ i,a i := Finset.sum_nonneg (fun i _ => ha i)
  by_cases h0 : ∑ i,a i = 0
  · have hall : ∀ i, a i = 0 := fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp h0 i (Finset.mem_univ i)
    simp [hall,xlog_zero]
  have hAp : 0 < ∑ i,a i := lt_of_le_of_ne hA (Ne.symm h0)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => log_ratio_lower (ha i) (hb i) hAp (hz i))
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,hb1,mul_one] at h
  dsimp [xlog]
  nlinarith

end RepeatedLocalization

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RepeatedLocalization.log_sum_inequality_oai.{u_1} := @OAI.RepeatedLocalization.log_sum_inequality_oai.{u_1}
