-- Prove2me | solution 1 for ModularCurve.finrank_parabolicHoms_le_two_mul_genusFormula
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1c1c96df-f2de-5249-b01b-3b1ff32f017f

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_CuspSpace
import Theorems.Thm_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index
import Theorems.Thm_ModularCurve_natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo
import Theorems.Thm_ModularCurve_natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_genusFormula
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

theorem solution (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [CharZero K] :
    (Module.finrank K (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K) : ℚ) ≤
      2 * ModularCurve.genusFormula N := by
  have hE := ModularCurve.Period.six_mul_finrank_parabolicHoms_add_le_index N K
  rw [ModularCurve.natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo N,
    ModularCurve.natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree N,
    ModularCurve.Gamma0_index N,
    ModularCurve.CuspSpace.card_cuspSpace_eq_cuspCount (NeZero.ne N)] at hE
  have hQ : (6 * Module.finrank K
        (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K)
      + 6 * ModularCurve.cuspCount N + 3 * ModularCurve.nuTwo N + 4 * ModularCurve.nuThree N : ℚ)
      ≤ 12 + ModularCurve.dedekindPsi N := by
    exact_mod_cast hE
  unfold ModularCurve.genusFormula
  linarith

end S_ModularCurve_finrank_parabolicHoms_le_two_mul_genusFormula
end P2MW
export P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_genusFormula (solution)
