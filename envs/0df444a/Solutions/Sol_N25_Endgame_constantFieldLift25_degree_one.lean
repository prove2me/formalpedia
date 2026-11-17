-- Prove2me | solution 1 for N25.Endgame.constantFieldLift25_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:05.576372+00:00
-- url     : https://prove2.me/submissions/cc4039bf-04fb-44c5-b286-45466949a90d

import Definitions.Def_N25_ConstantFieldLift
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField

set_option autoImplicit false

open ModularCurve AlgebraicCurve

namespace N25.Endgame

theorem _root_.solution (P : QPlace) (hP : P.deg = 1)
    (P' : GPlace) (hLift : IsConstantFieldLift25 P P') : P'.deg = 1 := by
  clear hP hLift
  let : IsCurveOver Qbar FG :=
    (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField Qbar 25 N25.H25).1
  exact IsCurveOver.deg_eq_one_of_isAlgClosed P'

end N25.Endgame
