-- Prove2me | solution 1 for ModularCurve.qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/04005aa6-ae17-59a7-8ad9-8412a7ccc076

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
import Theorems.Thm_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul

set_option autoImplicit false

open AlgebraicCurve
open scoped MatrixGroups

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectField K] (Γ : Subgroup SL(2, ℤ))
    (w : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.qExpFrobeniusPlaceModL K Γ p w = ModularCurve.qExpArithFrobC p K Γ • w :=
  AlgebraicCurve.Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow p (Fact.out : p.Prime).ne_zero
    (ModularCurve.qExpArithFrobC p K Γ) (ModularCurve.qExpFrobeniusModL K Γ p)
    (ModularCurve.qExpFrobeniusModL_isIntegral K Γ p)
    (ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow p K Γ) w

#print axioms solution

end S_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
end P2MW
export P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul (solution)
