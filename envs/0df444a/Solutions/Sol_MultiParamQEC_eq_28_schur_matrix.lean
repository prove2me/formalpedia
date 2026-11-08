-- Prove2me | solution 1 for MultiParamQEC.eq_28_schur_matrix
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:51:23.876789+00:00
-- url     : https://prove2.me/submissions/e1c196ff-0e6a-4eb1-914a-e4d7761ea41a

import Mathlib

open scoped Matrix

theorem solution {P : ℕ} (Y K : Matrix (Fin P) (Fin P) ℝ) (hK : K.IsHermitian) :
    (Matrix.fromBlocks Y K K 1).PosSemidef ↔ (Y - K * K).PosSemidef := by
  haveI : Invertible (1 : Matrix (Fin P) (Fin P) ℝ) := invertibleOne
  have h := Matrix.PosDef.fromBlocks₂₂ Y K (D := (1 : Matrix (Fin P) (Fin P) ℝ))
    Matrix.PosDef.one
  rw [hK.eq, inv_one, Matrix.mul_one] at h
  exact h
