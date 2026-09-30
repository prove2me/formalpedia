-- Prove2me | solution 1 for InventoryControl.cs_stage1_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T14:20:32.651246+00:00
-- url     : https://prove2.me/submissions/f345a234-9a93-4a0e-a105-817859d7bc0d

import Mathlib
import Definitions.Def_InventoryControl_clarkScarf

open MeasureTheory ProbabilityTheory in
lemma p2d7_gauss_map (m s : ℝ) :
    gaussianReal m (Real.toNNReal (s ^ 2)) = (gaussianReal 0 1).map (fun z => s * z + m) := by
  have h : gaussianReal m (Real.toNNReal (s ^ 2))
      = ((gaussianReal 0 1).map (s * ·)).map (· + m) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [sq_nonneg]
  rw [h, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p2d7_loss_std (z0 : ℝ) :
    ∫ z, max (z - z0) 0 ∂(gaussianReal 0 1) = normalLoss z0 := by
  unfold normalLoss
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext v
  simp only [Set.indicator, Set.mem_Ioi, smul_eq_mul]
  split_ifs with h
  · rw [max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith)]
    ring

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p2d7_loss (m s y : ℝ) (hs : 0 < s) :
    ∫ x, max (x - y) 0 ∂(gaussianReal m (Real.toNNReal (s ^ 2)))
      = s * normalLoss ((y - m) / s) := by
  rw [p2d7_gauss_map m s, integral_map (by fun_prop) (by fun_prop)]
  rw [← p2d7_loss_std, ← integral_const_mul]
  congr 1
  funext z
  rw [mul_max_of_nonneg _ _ hs.le, mul_zero]
  congr 1
  field_simp
  ring

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (e1 e2 b1 mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (y : ℝ) :
    csStage1Cost e1 e2 b1 mu sigma L1 y
      = e1 * y - (e1 + e2) * ((L1 + 1) * mu)
        + (e1 + e2 + b1) * (Real.sqrt (L1 + 1) * sigma)
            * normalLoss ((y - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) := by
  have hpos : 0 < Real.sqrt (((L1 + 1 : ℕ) : ℝ)) * sigma :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hs
  unfold csStage1Cost csDemand newsboyDemand
  rw [p2d7_loss _ _ _ hpos]
  push_cast
  ring
