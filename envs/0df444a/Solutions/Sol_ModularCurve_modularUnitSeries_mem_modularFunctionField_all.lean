-- Prove2me | solution 1 for ModularCurve.modularUnitSeries_mem_modularFunctionField_all
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/84df17a7-342d-5dc5-9be7-521c14997d27

import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionField_all
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

theorem solution (N : ℕ) [NeZero N] :
    ModularCurve.modularUnitSeries N ∈ ModularCurve.modularFunctionField N := by
  have h := ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC ℚ 0 N
    (fun h0 => NeZero.ne N (zero_dvd_iff.mp h0))
  rw [ModularCurve.modularFunctionFieldC_rat, ModularCurve.modularFunctionFieldFullC_rat] at h
  rw [h]
  exact ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull N

end S_ModularCurve_modularUnitSeries_mem_modularFunctionField_all
end P2MW
export P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionField_all (solution)
