-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:07:49.738794+00:00
-- url     : https://prove2.me/submissions/e61be9c7-ccf2-4e00-9cef-7a12c7a907b7

module
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_mulVec_norm_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_eq_jacobianMatrix


set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x h : Vec3) (hx : x ≠ 0) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      ((1 / ‖x‖ ^ 3) *
        (c.gravitationalParameter * candidateMaximum)) * ‖h‖ := by
  rw [c.accelerationField_fderiv_eq_jacobianMatrix x h hx]
  exact newtonianJacobianMatrix_mulVec_norm_le_candidateMaximum
    c.gravitationalParameter x h c.gravitationalParameter_nonneg hx
end NewtonianPointSource
end NewtonianLipschitz
