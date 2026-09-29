-- Prove2me | solution 1 for ModularCurve.towerSubstBar_finiteAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4e5662d8-edcb-5120-9d6f-29b89d054b80

import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_ModularCurve_towerInclBar_finiteAlong
import Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_towerSubstBar_finiteAlong
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (h : N * ℓ ∣ M) : FiniteAlong L (towerSubstBar L N ℓ h) := by
  rw [towerSubstBar]
  exact AlgebraicCurve.finiteAlong_comp _ _ (ModularCurve.finiteAlong_heckeBetaBar_of_prime L N ℓ)
    (ModularCurve.towerInclBar_finiteAlong L h)

end S_ModularCurve_towerSubstBar_finiteAlong
end P2MW
export P2MW.S_ModularCurve_towerSubstBar_finiteAlong (solution)
