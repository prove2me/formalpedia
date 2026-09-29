-- Prove2me | solution 1 for ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6c5429b6-17b6-541b-80a7-25b82136e70d

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow

set_option autoImplicit false

open AlgebraicCurve
open scoped MatrixGroups

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectField K] (Γ : Subgroup SL(2, ℤ))
    (f : ModularCurve.qExpFunctionFieldC K Γ) :
    ModularCurve.qExpFrobeniusModL K Γ p f = ((ModularCurve.qExpArithFrobC p K Γ)⁻¹ • f) ^ p := by
  apply Subtype.ext
  rw [ModularCurve.coe_qExpFrobeniusModL]
  change ModularCurve.qExpand K p (f : LaurentSeries K) =
    (((ModularCurve.qExpArithFrobC p K Γ)⁻¹ • f : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K) ^ p
  rw [ModularCurve.pow_char_eq_coeffMap_frobenius_qExpand p
      (((ModularCurve.qExpArithFrobC p K Γ)⁻¹ • f : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K),
    ModularCurve.coeffSemilinearAut.coeffMap_qExpand, ← ModularCurve.coe_qExpArithFrobC_smul, smul_inv_smul]

#print axioms solution

end S_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
end P2MW
export P2MW.S_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow (solution)
