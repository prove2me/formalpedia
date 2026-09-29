-- Prove2me | solution 1 for ModularCurve.place_deg_eq_one_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/00ec30ad-af44-5a46-b108-7c0cd552c31a

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_ne_zero_modularFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_place_deg_eq_one_of_isAlgClosed
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
open ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution (K : Type*) [Field K] [IsAlgClosed K]
    (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) : w.deg = 1 :=
  Place.deg_eq_one_of_isAlgClosed w (deg_ne_zero_modularFunctionFieldC K N w)

end S_ModularCurve_place_deg_eq_one_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_place_deg_eq_one_of_isAlgClosed (solution)
