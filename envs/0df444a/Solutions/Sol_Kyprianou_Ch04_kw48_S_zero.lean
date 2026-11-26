-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_S_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:43:22.094073+00:00
-- url     : https://prove2.me/submissions/397303cd-ab35-4e1e-b35b-c74a199f6312

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The record-level primitive vanishes at the initial time. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) (w : Ω) :
    S L beta 0 w = 0 := by
  have hU : runningSup L 0 w = 0 := by
    rw [Kyprianou.Ch04.kw47_runningSup_raw_eq]
    have hset : (Iic (0:NNReal)) = {0} := by ext t; simp
    rw [hset]
    simp [L.X_zero]
  simp [S,hU,integral_Icc_eq_integral_Ioc]
