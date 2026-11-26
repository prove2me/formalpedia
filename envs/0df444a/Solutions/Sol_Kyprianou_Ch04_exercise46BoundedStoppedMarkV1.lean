-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BoundedStoppedMarkV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:23:12.012238+00:00
-- url     : https://prove2.me/submissions/235db423-d61d-4421-a4c1-1e79ed241067

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_bounded_stop_eval_measurable
import Theorems.Thm_Kyprianou_Ch04_exercise46CappedPathJointV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BoundedLeftEvalV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (a : Omega → NNReal) (ha : IsStoppingTime G.rightCont (fun w => (a w : WithTop NNReal)))
    (T : NNReal) (hT : ∀ w, a w ≤ T) :
    Measurable[G.rightCont T] (fun w =>
      -(L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w))) := by
  have hX := Kyprianou.Ch08.StageB.p2m810_bounded_stop_eval_measurable
    G.rightCont L.X (fun t => (L.adapted t).mono (G.le_rightCont t) le_rfl)
    L.rightCont a ha T hT
  have haM : Measurable[G.rightCont T] a := by
    simpa only [WithTop.untopD_coe] using
      Measurable.untopD (0 : NNReal)
        (ha.measurable_of_le (fun w => WithTop.coe_le_coe.mpr (hT w)))
  have hY := Kyprianou.Ch04.exercise46BoundedLeftEvalV1 P G L a T hT haM
    (Kyprianou.Ch04.exercise46CappedPathJointV1 P G L T)
  exact (hX.sub hY).neg
