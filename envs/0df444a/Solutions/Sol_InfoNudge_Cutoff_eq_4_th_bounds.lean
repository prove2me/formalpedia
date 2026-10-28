-- Prove2me | solution 1 for InfoNudge.Cutoff.eq_4_th_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:34:01.882013+00:00
-- url     : https://prove2.me/submissions/d2ff22e9-29d5-436c-b70d-734653641c55

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

open InfoNudge.Cutoff in
theorem solution (M : Params) (hS : Standing M) :
    0 < ta M ∧ ta M < 1 ∧ 0 < th M ∧ th M < ta M := by
  obtain ⟨hβ0, hβ1, hδ0, hδ1, hK, _, _⟩ := hS
  have hK0 : 0 < M.β * M.δ ^ 2 * M.C := by linarith
  have ta0 : 0 < ta M := by unfold ta; exact div_pos one_pos hK0
  have ta1 : ta M < 1 := by unfold ta; rw [div_lt_one hK0]; exact hK
  have hβδ : 0 < M.β * M.δ := mul_pos hβ0 hδ0
  have f0 : 0 < (1 + M.β * M.δ) / (1 + M.δ) := div_pos (by linarith) (by linarith)
  have f1 : (1 + M.β * M.δ) / (1 + M.δ) < 1 := by
    rw [div_lt_one (by linarith)]
    nlinarith
  refine ⟨ta0, ta1, ?_, ?_⟩
  · unfold th; exact mul_pos f0 ta0
  · unfold th
    calc (1 + M.β * M.δ) / (1 + M.δ) * ta M < 1 * ta M := mul_lt_mul_of_pos_right f1 ta0
      _ = ta M := one_mul _
