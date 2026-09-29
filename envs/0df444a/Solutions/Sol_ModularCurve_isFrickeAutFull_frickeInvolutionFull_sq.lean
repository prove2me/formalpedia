-- Prove2me | solution 1 for ModularCurve.isFrickeAutFull_frickeInvolutionFull_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0fc8bdb4-b638-508e-9608-0edee1f945a9

import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_sq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p)) :=
  isFrickeAutFull_frickeInvolutionFull (p * p) (exists_isFrickeAutFull_sq p)

end S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_sq
end P2MW
export P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_sq (solution)
