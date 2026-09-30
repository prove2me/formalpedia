-- Prove2me | solution 1 for InventoryControl.cs_stage1_period_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:32:25.625882+00:00
-- url     : https://prove2.me/submissions/5f48730f-c86b-427e-b7b6-6873d373c343

import Mathlib
import Definitions.Def_InventoryControl_clarkScarf

open MeasureTheory ProbabilityTheory

lemma invCtrl_csDemand_posneg (mu sigma : ℝ) (n : ℕ) (y : ℝ) :
    (∫ x, max (y - x) 0 ∂(InventoryControl.csDemand mu sigma n))
      - (∫ x, max (x - y) 0 ∂(InventoryControl.csDemand mu sigma n)) = y - n * mu := by
  unfold InventoryControl.csDemand InventoryControl.newsboyDemand
  have hid : Integrable (fun x : ℝ => x)
      (gaussianReal ((n : ℝ) * mu) (Real.toNNReal ((Real.sqrt n * sigma) ^ 2))) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h1 : Integrable (fun x : ℝ => y - x)
      (gaussianReal ((n : ℝ) * mu) (Real.toNNReal ((Real.sqrt n * sigma) ^ 2))) :=
    (integrable_const y).sub hid
  have h2 : Integrable (fun x : ℝ => x - y)
      (gaussianReal ((n : ℝ) * mu) (Real.toNNReal ((Real.sqrt n * sigma) ^ 2))) :=
    hid.sub (integrable_const y)
  rw [← integral_sub h1.pos_part h2.pos_part]
  have hpt : (fun x : ℝ => max (y - x) 0 - max (x - y) 0) = fun x => y - x := by
    funext x
    rcases le_total x y with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  rw [hpt, integral_sub (integrable_const y) hid, integral_const, integral_id_gaussianReal]
  simp

open InventoryControl in
theorem solution (e1 e2 b1 mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (y1 : ℝ) :
    (e1 + e2) * (∫ x, max (y1 - x) 0 ∂(csDemand mu sigma (L1 + 1)))
        + b1 * (∫ x, max (x - y1) 0 ∂(csDemand mu sigma (L1 + 1)))
      = (e1 + e2) * (y1 - (L1 + 1) * mu)
        + (e1 + e2 + b1) * ∫ x, max (x - y1) 0 ∂(csDemand mu sigma (L1 + 1)) := by
  have key := invCtrl_csDemand_posneg mu sigma (L1 + 1) y1
  push_cast at key
  have e : (∫ x, max (y1 - x) 0 ∂(csDemand mu sigma (L1 + 1)))
      = (y1 - ((L1 : ℝ) + 1) * mu) + ∫ x, max (x - y1) 0 ∂(csDemand mu sigma (L1 + 1)) := by
    linarith
  rw [e]
  ring
