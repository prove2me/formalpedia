-- Prove2me | solution 1 for ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/264ca020-285b-5774-b841-1c40493ea88e

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [Field K]
    (ℓ : ℕ) [CharP K ℓ] (N : ℕ) [NeZero N] (hlN : ¬ ℓ ∣ N) :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N := by
  rcases eq_or_ne ℓ 0 with hℓ | hℓ
  ·
    subst hℓ
    haveI : CharZero K := CharP.charP_to_charZero K
    exact modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero K N
  ·
    haveI : NeZero ℓ := ⟨hℓ⟩
    exact modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos K ℓ N hlN

end S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
end P2MW
export P2MW.S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC (solution)
