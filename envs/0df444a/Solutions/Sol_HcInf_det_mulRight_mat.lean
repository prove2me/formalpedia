-- Prove2me | solution 1 for HcInf.det_mulRight_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:07.285002+00:00
-- url     : https://prove2.me/submissions/00d1b10e-b593-40bc-bd42-56dd84516a06

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HuaInvOfTauDeriv

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
theorem _root_.solution (B : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulRight ℂ B : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      B.det ^ Fintype.card n := by
  classical
  let e : Matrix n n ℂ ≃ₗ[ℂ] (n → n → ℂ) :=
    { toFun := fun X i j => X i j
      invFun := fun v => Matrix.of v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g : (n → n → ℂ) →ₗ[ℂ] (n → n → ℂ) :=
    LinearMap.pi fun i => (Matrix.toLin' Bᵀ).comp (LinearMap.proj i)
  have key : (LinearMap.mulRight ℂ B : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      (e.symm : (n → n → ℂ) →ₗ[ℂ] Matrix n n ℂ).comp
        (g.comp (e.symm.symm : Matrix n n ℂ →ₗ[ℂ] (n → n → ℂ))) := by
    refine LinearMap.ext fun X => ?_
    refine Matrix.ext fun i j => ?_
    rw [LinearMap.mulRight_apply, Matrix.mul_apply]
    change ∑ k, X i k * B k j = ∑ k, B k j * X i k
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [key, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose]
end HcInf
