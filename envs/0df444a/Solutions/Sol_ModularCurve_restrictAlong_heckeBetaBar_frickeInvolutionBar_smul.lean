-- Prove2me | solution 1 for ModularCurve.restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d287395f-56fb-5c26-9c12-6e142fbcb887

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
import Theorems.Thm_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

theorem solution (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
      = W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα := by
  rw [Place.smul_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
      (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hβ hα (frickeInvolutionBar (1 * q)) 1
      (fun x => ?_) W, one_smul]
  rw [AlgEquiv.one_apply]
  exact (DFunLike.congr_fun (frickeInvolutionBar_comp_heckeAlphaBar_one q) x).symm

end S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
end P2MW
export P2MW.S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul (solution)
