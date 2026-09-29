-- Prove2me | solution 1 for ModularCurve.x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/14288106-37c9-5c13-8726-7f812cf51e39

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_CongruenceSubgroup_gamma1_inf_gamma0_mul_eq_gammaH_ker
import Theorems.Thm_CongruenceSubgroup_gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (K : Type*) [Field K] (M₀ q : ℕ)
    [NeZero M₀] [NeZero q] (h : Nat.Coprime M₀ q) :
    ModularCurve.x1x0FunctionFieldC K M₀ q =
      ModularCurve.xHFunctionFieldC K (M₀ * q) (ZMod.unitsMap (dvd_mul_right M₀ q)).ker := by
  rw [ModularCurve.x1x0FunctionFieldC, ModularCurve.xHFunctionFieldC,
    CongruenceSubgroup.gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime M₀ q h,
    CongruenceSubgroup.gamma1_inf_gamma0_mul_eq_gammaH_ker]

namespace ModularCurve p2m_export "ModularCurve" "x1x0FunctionFieldC laurentBaseChange xHFunctionFieldC xHFunctionFieldBar" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.laurentBaseChange_x1x0FunctionFieldC_eq_xHFunctionFieldBar (M₀ q : ℕ) [NeZero M₀] [NeZero q]
    (h : Nat.Coprime M₀ q) :
    ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ q) =
      ModularCurve.xHFunctionFieldBar (M₀ * q) (ZMod.unitsMap (dvd_mul_right M₀ q)).ker := by
  rw [solution ℚ M₀ q h]

end S_ModularCurve_x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker
end P2MW
export P2MW.S_ModularCurve_x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker (solution)
