-- Prove2me | solution 1 for ModularCurve.genusFormula_mul_expand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/01a6684d-40bf-5bf1-9a0c-2902e5420abb

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_nuTwo_mul_of_coprime
import Theorems.Thm_ModularCurve_nuThree_mul_of_coprime
import Theorems.Thm_ModularCurve_cuspCount_mul_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFormula_mul_expand
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

open ModularCurve

theorem solution {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (h : Nat.Coprime M N) :
    genusFormula (M * N) - 2 * genusFormula N + 1
      = ((dedekindPsi M : ℚ) - 2) * (dedekindPsi N : ℚ) / 12
        - ((nuTwo M : ℚ) - 2) * (nuTwo N : ℚ) / 4
        - ((nuThree M : ℚ) - 2) * (nuThree N : ℚ) / 3
        - ((cuspCount M : ℚ) - 2) * (cuspCount N : ℚ) / 2 :=
  by
    unfold genusFormula
    rw [dedekindPsi_mul_of_coprime M N h, nuTwo_mul_of_coprime h, nuThree_mul_of_coprime h,
      cuspCount_mul_of_coprime hM hN h]
    push_cast
    ring

end S_ModularCurve_genusFormula_mul_expand
end P2MW
export P2MW.S_ModularCurve_genusFormula_mul_expand (solution)
