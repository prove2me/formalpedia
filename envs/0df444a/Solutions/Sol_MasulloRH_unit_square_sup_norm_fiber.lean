-- Prove2me | solution 1 for MasulloRH.unit_square_sup_norm_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:15:45.380021+00:00
-- url     : https://prove2.me/submissions/e58d674b-f310-4103-bc4e-01ad32ef5125

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum

open Set

private theorem unit_square_face_fiber :
    {t : ℝ | ‖fun i : Fin 2 => if i = 0 then (1 : ℝ) else t‖ = 1} = Icc (-1) 1 := by
  ext t
  let v : Fin 2 → ℝ := fun i => if i = 0 then 1 else t
  change ‖v‖ = 1 ↔ -1 ≤ t ∧ t ≤ 1
  have hone : 1 ≤ ‖v‖ := by simpa [v] using norm_le_pi_norm v 0
  have ht : |t| ≤ ‖v‖ := by simpa [v, Real.norm_eq_abs] using norm_le_pi_norm v 1
  constructor
  · intro h
    exact abs_le.mp (h ▸ ht)
  · intro h
    apply le_antisymm _ hone
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases hi : i = 0
    · simp [v, hi]
    · simpa [v, hi, Real.norm_eq_abs] using abs_le.mpr h

theorem solution :
    let S := {t : ℝ | ‖fun i : Fin 2 => if i = 0 then (1 : ℝ) else t‖ = 1}
    S = Icc (-1) 1 ∧ S.Infinite := by
  change _ = Icc (-1) 1 ∧ _
  refine ⟨unit_square_face_fiber, ?_⟩
  rw [unit_square_face_fiber]
  exact Set.Icc_infinite (by norm_num)
