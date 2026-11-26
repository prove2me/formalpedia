-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46CappedPathJointV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:42:08.558595+00:00
-- url     : https://prove2.me/submissions/726472b7-efa9-4f34-9823-4dcf1ce5be97

import Mathlib
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G) (T : NNReal) :
    @Measurable (NNReal × Omega) Real
      (@Prod.instMeasurableSpace NNReal Omega inferInstance (G.rightCont T))
      inferInstance (fun z => L.X (min z.1 T) z.2) := by
  let F : NNReal → Omega → Real := fun t w => L.X (min t T) w
  have hF (t : NNReal) : Measurable[G.rightCont T] (F t) :=
    (L.adapted (min t T)).mono
      ((G.le_rightCont (min t T)).trans (G.rightCont.mono (min_le_right _ _))) le_rfl
  have hFR (w : Omega) (t : NNReal) :
      ContinuousWithinAt (fun u => F u w) (Ici t) t := by
    have hm : MapsTo (fun u : NNReal => min u T) (Ici t) (Ici (min t T)) :=
      fun u hu => min_le_min_right T hu
    have hc : ContinuousWithinAt (fun u : NNReal => min u T) (Ici t) t :=
      (continuous_id.min continuous_const).continuousWithinAt
    change ContinuousWithinAt ((fun u => L.X u w) ∘ (fun u : NNReal => min u T)) (Ici t) t
    exact ContinuousWithinAt.comp_of_eq (f := fun u : NNReal => min u T)
      (L.rightCont w (min t T)) hc hm rfl
  exact @rightContinuous_measurable_sections_joint_evaluation Omega
    (G.rightCont T) F hF hFR
