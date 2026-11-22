-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_family_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T02:24:09.202623+00:00
-- url     : https://prove2.me/submissions/24692409-946e-4c8e-b65d-56c67cb3601c

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_L1_cap_and_ratio_bound
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_singleton_markov
open MeasureTheory ProbabilityTheory Filter Set Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d))
    (ρd : ℝ → Measure ℝ)
    (hρd : ∀ d : ℝ, 0 < d →
      IsProbabilityMeasure (ρd d) ∧ (ρd d) (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)).toReal =
          f d * (1 - s / d))
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun d : ℝ => (ρd d) {x}) atTop (nhds (0 : ℝ≥0∞)) := by
  classical
  have hcpos : 0 < 1 - Real.exp (-x) := sub_pos.mpr (by rw [Real.exp_lt_one_iff]; linarith)
  set cE : ℝ≥0∞ := ENNReal.ofReal (1 - Real.exp (-x)) with hcE
  have hcEne0 : cE ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcpos)
  obtain ⟨hL1all, hfdgt, -⟩ :=
    Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap_and_ratio_bound f hpos hdraw ρd hρd
  have hfinal_le : ∀ d : ℝ, 0 < d → (ρd d) {x} ≤
      cE⁻¹ * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d))) := by
    intro d hd
    obtain ⟨hprob, hsupp, _⟩ := hρd d hd; haveI := hprob
    have h := Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_markov (ρd d) hsupp x hx
    simpa [hcE, ENNReal.ofReal_inv_of_pos hcpos] using h
  have hDle : ∀ d : ℝ, 1 < d → 1 - ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)).toReal) ≤ 1 / d := by
    intro d hd1
    have hd0 : 0 < d := lt_trans one_pos hd1
    obtain ⟨_, _, heq⟩ := hρd d hd0
    have heq1 := heq 1 one_pos
    obtain ⟨-, hl1pos, hl1le⟩ := hL1all d hd0
    have hfd : 0 < f d := hpos d hd0
    have hf1 : 0 < f 1 := hpos 1 one_pos
    have hgt := hfdgt d hd1
    have hdne : d ≠ 0 := ne_of_gt hd0
    have hsub_ne : f d - f 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hgt)
    field_simp at heq1 ⊢
    nlinarith [heq1, hfd, hf1, hd0, hd1, hl1pos, hl1le, hgt]
  have hEnn_le : ∀ d : ℝ, 1 < d → (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d))) ≤
      ENNReal.ofReal (1 / d) := by
    intro d hd1
    have hd0 : 0 < d := lt_trans one_pos hd1
    obtain ⟨hle1, hl1pos, -⟩ := hL1all d hd0
    have hl1nn : 0 ≤ ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)).toReal) := hl1pos.le
    have hid : (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d))) =
        ENNReal.ofReal (1 - ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)).toReal)) := by
      have hsub := ENNReal.ofReal_sub (1 : ℝ) hl1nn
      have hto : ENNReal.ofReal (((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)).toReal)) =
          (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)) :=
        ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt hle1 ENNReal.one_lt_top))
      rw [hto] at hsub
      simpa [ENNReal.ofReal_one] using hsub.symm
    rw [hid]; exact ENNReal.ofReal_le_ofReal (hDle d hd1)
  have hupper_tend : Tendsto (fun d : ℝ => ENNReal.ofReal (1 / d)) atTop (nhds 0) := by
    simpa [one_div, ENNReal.ofReal_zero, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  have hgap_tend : Tendsto (fun d : ℝ => 1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d))) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_tend
    · filter_upwards with d; exact zero_le
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with d hd1; exact hEnn_le d hd1
  have hKfin : cE⁻¹ ≠ ⊤ := by rw [ENNReal.inv_ne_top]; exact hcEne0
  have hK_tend : Tendsto (fun d : ℝ => cE⁻¹ * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)))) atTop (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul hgap_tend (Or.inr hKfin)
    simpa [mul_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK_tend
  · filter_upwards with d; exact zero_le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd; exact hfinal_le d hd
