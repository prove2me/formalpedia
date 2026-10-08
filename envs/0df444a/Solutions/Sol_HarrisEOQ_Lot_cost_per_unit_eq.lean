-- Prove2me | solution 1 for HarrisEOQ.Lot.cost_per_unit_eq
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:56:29.346869+00:00
-- url     : https://prove2.me/submissions/87fb98d5-e501-4b33-9953-7fcad8b67b26

import Mathlib
import Definitions.Def_HarrisEOQ_Lot_Setting

set_option autoImplicit false

open HarrisEOQ.Lot

theorem solution (M C S X : ℝ) (hM : 0 < M) :
    interestPerPiece M C S X = 1 / (240 * M) * (C * X + S) ∧
      costPerUnit M C S X = interestPerPiece M C S X + S / X + C := by
  have h : interestPerPiece M C S X = 1 / (240 * M) * (C * X + S) := by
    unfold interestPerPiece
    field_simp
    ring
  exact ⟨h, by rw [h]; rfl⟩

#print axioms solution
