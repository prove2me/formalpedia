-- Prove2me | solution 1 for OAI.StrictInverseFirstPower.koebe_quarter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:28:04.592985+00:00
-- url     : https://prove2.me/submissions/bff48d9d-33ec-4000-b584-0fb6512dd590

import Mathlib
import Theorems.Thm_OAI_StrictInverseFirstPower_second_coefficient_le_two

section
-- module Solutions.OAIQW_StrictInverseFirstPower.ImageBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Metric Complex
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma omitted_mobius_normalized {f : ℂ → ℂ} {c : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 1 - c * f z ≠ 0) :
    DifferentiableOn ℂ (fun z => f z / (1 - c * f z)) (ball 0 1) ∧
    InjOn (fun z => f z / (1 - c * f z)) (ball 0 1) ∧
    (f 0 / (1 - c * f 0) = 0) ∧
    deriv (fun z => f z / (1 - c * f z)) 0 = 1 := by
  refine ⟨hd.div ((differentiableOn_const (1 : ℂ)).sub (hd.const_mul c)) hn, ?_, by simp [h0], ?_⟩
  · intro z hz w hw he
    apply hi hz hw
    have he' := (div_eq_div_iff (hn z hz) (hn w hw)).mp he
    linear_combination he'
  · have hdf : HasDerivAt f 1 0 := by
      simpa only [h1] using (hd.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))).hasDerivAt
    have he := hdf.div ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) (hn 0 (by simp))
    convert he.deriv using 1 <;> first | rfl | simp [h0]

lemma omitted_mobius_coefficient {f : ℂ → ℂ} {c : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    deriv (dslope (fun z => f z / (1 - c * f z)) 0) 0 =
      deriv (dslope f 0) 0 + c := by
  let g : ℂ → ℂ := fun z => f z / (1 - c * f z)
  have hd0 := hd.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hdf : HasDerivAt f 1 0 := by simpa only [h1] using hd0.hasDerivAt
  have hn0 : 1 - c * f 0 ≠ 0 := by simp [h0]
  have hgd : HasDerivAt g 1 0 := by
    convert hdf.div ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) hn0 using 1
    all_goals first | rfl | simp [h0]
  have hg0 : g 0 = 0 := by simp [g, h0]
  have he (z : ℂ) : dslope g 0 z = dslope f 0 z / (1 - c * f z) := by
    by_cases hz : z = 0
    · simp [hz, hgd.deriv, h0, h1]
    · simp only [dslope_of_ne _ hz, slope_def_field, sub_zero, hg0, h0]
      dsimp only [g]
      ring
  have hdU := ((Complex.differentiableOn_dslope
    (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))).mpr hd).differentiableAt
      (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hp := hdU.hasDerivAt.div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) hn0
  have hpe : HasDerivAt (dslope g 0) (deriv (dslope f 0) 0 + c) 0 := by
    convert hp using 1
    all_goals first | rfl | exact funext he | simp [h0, h1]
  exact hpe.deriv

theorem omitted_value_quarter {f : ℂ → ℂ} {w : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (hw : w ∉ f '' ball 0 1) :
    (1 / 4 : ℝ) ≤ ‖w‖ := by
  have hw0 : w ≠ 0 := by
    intro he
    apply hw
    exact ⟨0, by simp, by rw [h0, he]⟩
  have hn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 1 - w⁻¹ * f z ≠ 0 := by
    intro he
    apply hw
    refine ⟨z, hz, ?_⟩
    have ha : w⁻¹ * f z = 1 := (sub_eq_zero.mp he).symm
    calc f z = w * (w⁻¹ * f z) := by rw [← mul_assoc, mul_inv_cancel₀ hw0, one_mul]
         _ = w := by rw [ha, mul_one]
  obtain ⟨hgd, hgi, hg0, hg1⟩ := omitted_mobius_normalized hd hi h0 h1 hn
  have ha := second_coefficient_le_two hd hi h0 h1
  have hb := second_coefficient_le_two hgd hgi hg0 hg1
  rw [omitted_mobius_coefficient hd h0 h1] at hb
  have hc : ‖w⁻¹‖ ≤ 4 := by
    calc ‖w⁻¹‖ = ‖(deriv (dslope f 0) 0 + w⁻¹) - deriv (dslope f 0) 0‖ := by ring_nf
         _ ≤ ‖deriv (dslope f 0) 0 + w⁻¹‖ + ‖deriv (dslope f 0) 0‖ := norm_sub_le _ _
         _ ≤ 4 := by linarith
  rw [norm_inv] at hc
  have hnpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hh := mul_le_mul_of_nonneg_right hc hnpos.le
  rw [inv_mul_cancel₀ (ne_of_gt hnpos)] at hh
  linarith

theorem koebe_quarter_oai {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ball (0 : ℂ) (1 / 4) ⊆ f '' ball 0 1 := by
  intro w hw
  by_contra hn
  have hh := omitted_value_quarter hd hi h0 h1 hn
  simp only [mem_ball, dist_zero_right] at hw
  linarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex
open scoped Topology

end

end OAI
end

theorem solution : type_of% @OAI.StrictInverseFirstPower.koebe_quarter_oai := @OAI.StrictInverseFirstPower.koebe_quarter_oai
