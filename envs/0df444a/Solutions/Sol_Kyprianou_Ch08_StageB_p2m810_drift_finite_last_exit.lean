-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_drift_finite_last_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:01:44.595627+00:00
-- url     : https://prove2.me/submissions/eefd9cef-f365-419a-9153-9ddbddca1a2d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (y : ℝ) (h : Tendsto f atTop atTop) :
    lastExitShifted (fun t (_ : Unit) => f t) y () ≠ ⊤ := by
  obtain ⟨b,hb⟩ := eventually_atTop.mp (tendsto_atTop.mp h (-y))
  have hle : lastExitShifted (fun t (_ : Unit) => f t) y () ≤
      (b : WithTop ℝ≥0) := by
    unfold lastExitShifted lastNegativeVisit
    apply sSup_le
    rintro _ ⟨u,hu,rfl,hneg⟩
    apply WithTop.coe_le_coe.mpr
    by_contra! hbu
    have hh := hb u hbu.le
    simp only [shifted] at hneg
    linarith
  exact ne_of_lt (hle.trans_lt (WithTop.coe_lt_top _))
