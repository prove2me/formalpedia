-- Prove2me | solution 1 for Kyprianou.Ch01.passageLaplaceDeficitGeOfPassageGeV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:18:24.770271+00:00
-- url     : https://prove2.me/submissions/a37395f1-ef5e-4310-b247-babc16eaedee

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : WithTop ℝ≥0) (ε : ℝ≥0)
    (hBound : (ε : WithTop ℝ≥0) ≤ T) :
    1 - Real.exp (-(ε : ℝ)) ≤
      1 - (match T with
        | none => (0 : ℝ)
        | some t => Real.exp (-(t : ℝ))) := by
  cases T with
  | top =>
      change 1 - Real.exp (-(ε : ℝ)) ≤ (1 : ℝ) - 0
      have hePos : 0 ≤ Real.exp (-(ε : ℝ)) :=
        (Real.exp_pos _).le
      linarith
  | coe t =>
      have ht : ε ≤ t := WithTop.coe_le_coe.mp hBound
      have htR : (ε : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast ht
      have hExp : Real.exp (-(t : ℝ)) ≤
          Real.exp (-(ε : ℝ)) := by
        apply Real.exp_le_exp.mpr
        linarith
      change 1 - Real.exp (-(ε : ℝ)) ≤
        1 - Real.exp (-(t : ℝ))
      linarith
