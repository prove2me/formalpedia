-- Prove2me | solution 1 for Kyprianou.Ch03.expClockRationalBetweenV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:42:38.697022+00:00
-- url     : https://prove2.me/submissions/ce46a7f8-e2ff-4a83-8bd1-98fbdf686dbc

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (a : WithTop NNReal) (b : NNReal) :
    a < (b : WithTop NNReal) ↔
      ∃ r : ℚ, a < ((r : ℝ).toNNReal : WithTop NNReal) ∧
        (r : ℝ).toNNReal < b := by
  constructor
  · intro h
    obtain ⟨u, hu, hub⟩ := WithTop.lt_iff_exists_coe_btwn.mp h
    obtain ⟨r, hr, hur, hrb⟩ := (NNReal.lt_iff_exists_rat_btwn u b).mp
      (WithTop.coe_lt_coe.mp hub)
    exact ⟨r, hu.trans (WithTop.coe_lt_coe.mpr hur), hrb⟩
  · rintro ⟨r, hr, hrb⟩
    exact hr.trans (WithTop.coe_lt_coe.mpr hrb)
