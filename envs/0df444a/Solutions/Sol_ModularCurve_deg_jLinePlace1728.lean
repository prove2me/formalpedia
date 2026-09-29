-- Prove2me | solution 1 for ModularCurve.deg_jLinePlace1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5f6bcf1c-a579-5ad7-b4fe-a50f72f40176

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_deg_jLinePlace1728

set_option autoImplicit false

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
attribute [local instance] ModularCurve.instDecidableEqRatFuncRat

theorem solution : ModularCurve.jLinePlace1728.deg = 1 := by
  unfold ModularCurve.jLinePlace1728
  rw [Place.deg_congrRingEquiv]
  exact deg_placeOfPoint ℚ 1728

end S_ModularCurve_deg_jLinePlace1728
end P2MW
export P2MW.S_ModularCurve_deg_jLinePlace1728 (solution)
