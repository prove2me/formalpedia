-- Prove2me | solution 1 for ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/38f26354-0a46-53a1-ac90-466bb3d6f3d5

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_order_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option maxHeartbeats 1600000 in
theorem solution (k : Type*) [Field k] [DecidableEq (RatFunc k)] :
    (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord
        ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) = -1 := by
  rw [ord_charLGeomPlaceEquiv_placeInfty_eq_order]
  exact order_jqModC k

end S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
end P2MW
export P2MW.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC (solution)
