-- Prove2me | solution 1 for HcInf.det_mulLeft_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:55.600405+00:00
-- url     : https://prove2.me/submissions/16208bf7-b2a1-458a-b96d-76584039e786

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HuaInvOfTauDeriv
import Theorems.Thm_HcInf_det_mulRight_mat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix
variable {n : Type} [Fintype n] [DecidableEq n]
namespace HcInf
theorem _root_.solution (A : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulLeft ℂ A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      A.det ^ Fintype.card n := by
  classical
  let e : Matrix n n ℂ ≃ₗ[ℂ] Matrix n n ℂ := Matrix.transposeLinearEquiv n n ℂ ℂ
  have key : (LinearMap.mulLeft ℂ A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      (e : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ).comp
        ((LinearMap.mulRight ℂ Aᵀ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ).comp
          (e.symm : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)) := by
    refine LinearMap.ext fun X => ?_
    simp [e, Matrix.transpose_mul]
  rw [key, LinearMap.det_conj, det_mulRight_mat, Matrix.det_transpose]
end HcInf
