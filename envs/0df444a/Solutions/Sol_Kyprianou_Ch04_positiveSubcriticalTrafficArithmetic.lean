-- Prove2me | solution 1 for Kyprianou.Ch04.positiveSubcriticalTrafficArithmetic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:30:43.419384+00:00
-- url     : https://prove2.me/submissions/b1753f71-2c27-4009-89da-b387d0f2ec38

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- Positive subcritical traffic implies a strictly smaller finite positive jump mean. -/
theorem solution (M : ENNReal) (d : ℝ) (hd : 0 < d)
    (hr0 : 0 < M / ENNReal.ofReal d) (hr1 : M / ENNReal.ofReal d < 1) :
    M ≠ ⊤ ∧ M ≠ 0 ∧ M.toReal < d := by
  let D := ENNReal.ofReal d
  have hMD : M < D := by
    change M / D < 1 at hr1
    rwa [ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top),one_mul] at hr1
  have hMtop : M ≠ ⊤ := ne_of_lt (hMD.trans_le le_top)
  have hM0 : M ≠ 0 := by
    intro h
    simp [h] at hr0
  have hDtop : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have h : M.toReal < D.toReal := (ENNReal.toReal_lt_toReal hMtop hDtop).mpr hMD
  exact ⟨hMtop,hM0,by simpa [D,ENNReal.toReal_ofReal hd.le] using h⟩
