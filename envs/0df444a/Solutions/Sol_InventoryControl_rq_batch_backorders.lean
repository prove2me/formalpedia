-- Prove2me | solution 1 for InventoryControl.rq_batch_backorders
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T18:24:07.43697+00:00
-- url     : https://prove2.me/submissions/b2a3e495-1734-4ba6-8308-b99fd7774ce3

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory in
private lemma p772_gauss_map (m s : ℝ) :
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
private lemma p772_loss_std (z0 : ℝ) :
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
private lemma p772_loss (m s y : ℝ) (hs : 0 < s) :
    ∫ x, max (x - y) 0 ∂(gaussianReal m (Real.toNNReal (s ^ 2)))
      = s * normalLoss ((y - m) / s) := by
  rw [p772_gauss_map m s, integral_map (by fun_prop) (by fun_prop)]
  rw [← p772_loss_std, ← integral_const_mul]
  congr 1
  funext z
  rw [mul_max_of_nonneg _ _ hs.le, mul_zero]
  congr 1
  field_simp
  ring

open MeasureTheory ProbabilityTheory in
private lemma p772_int (m s y : ℝ) :
    Integrable (fun x => max (x - y) 0) (gaussianReal m (Real.toNNReal (s ^ 2))) := by
  have h : Integrable (fun x : ℝ => x) (gaussianReal m (Real.toNNReal (s ^ 2))) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  exact (h.sub (integrable_const y)).pos_part

private lemma p772_pt (R Q u : ℝ) (hQ : 0 ≤ Q) :
    min (max (u - R) 0) Q = max (u - R) 0 - max (u - (R + Q)) 0 := by
  rcases le_total u R with h1 | h1
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), min_eq_left hQ]
    ring
  · rcases le_total u (R + Q) with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), min_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith), max_eq_left (by linarith), min_eq_right (by linarith)]
      ring

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (R Q m s : ℝ) (hQ : 0 ≤ Q) (hs : 0 < s) :
    rqBatchBackorders R Q m s
      = s * normalLoss ((R - m) / s) - s * normalLoss ((R + Q - m) / s) := by
  unfold rqBatchBackorders newsboyDemand
  simp_rw [p772_pt R Q _ hQ]
  rw [integral_sub (p772_int m s R) (p772_int m s (R + Q)), p772_loss m s R hs,
    p772_loss m s (R + Q) hs]
