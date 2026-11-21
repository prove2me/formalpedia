-- Prove2me | solution 1 for Kyprianou.Ch01.passageLaplaceDeficitEventSubsetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:22:12.134583+00:00
-- url     : https://prove2.me/submissions/25df54e3-c3d7-43b5-9e52-38b929c08e6e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ε : ℝ≥0) :
    {ω | (ε : WithTop ℝ≥0) ≤ firstUpperPassage X s ω} ⊆
      {ω | 1 - Real.exp (-(ε : ℝ)) ≤
        1 - passageLaplace (firstUpperPassage X s) 1 ω} := by
  intro ω hω
  cases hT : firstUpperPassage X s ω with
  | top =>
      have he : 0 ≤ Real.exp (-(ε : ℝ)) :=
        (Real.exp_pos _).le
      have hGoal :
          1 - Real.exp (-(ε : ℝ)) ≤ (1 : ℝ) - 0 := by
        linarith
      simpa [passageLaplace, hT] using hGoal
  | coe t =>
      have hTop : (ε : WithTop ℝ≥0) ≤
          (t : WithTop ℝ≥0) := by
        simpa [hT] using hω
      have ht : ε ≤ t := WithTop.coe_le_coe.mp hTop
      have htR : (ε : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast ht
      have he : Real.exp (-(t : ℝ)) ≤
          Real.exp (-(ε : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      have hGoal :
          1 - Real.exp (-(ε : ℝ)) ≤
            1 - Real.exp (-(t : ℝ)) := by
        linarith
      simpa [passageLaplace, hT] using hGoal
