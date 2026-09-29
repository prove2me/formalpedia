-- Prove2me | solution 1 for ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6831763e-50f8-5cd7-aa4e-183de9f70681

import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_heckeAlg_smul_comm_of_forall_gen
import Theorems.Thm_ModularCurve_heckePic0Bar_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N] (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) :
    letI := ModularCurve.heckeModuleBar N
    SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg
      (ModularCurve.JZero N) := by
  letI := heckeModuleBar N
  refine ⟨fun σ T x => ?_⟩
  let sp : JZero N →+ JZero N := DistribMulAction.toAddMonoidHom (JZero N) σ
  show sp (T • x) = T • sp x
  refine heckeAlg_smul_comm_of_forall_gen sp (fun ℓ y => ?_) T x
  show σ • (heckeGen ℓ • y) = heckeGen ℓ • (σ • y)
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  rw [heckeModuleBar_heckeGen_smul hcomm, heckeModuleBar_heckeGen_smul hcomm,
    heckeOperatorBar_apply, heckeOperatorBar_apply]
  by_cases hin : HeckeInputsAlong (AlgebraicClosure ℚ) N (ℓ : ℕ)
  · obtain ⟨hα, hβ, hP, hfin, hFI, hN⟩ := hin
    haveI := hP
    rw [heckeOperatorAlong_eq hα hβ hFI hfin hN]
    exact (heckePic0Bar_smul hα hβ hFI hfin hN σ y).symm
  · rw [heckeOperatorAlong_of_not hin]
    simp

end S_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
end P2MW
export P2MW.S_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar (solution)
