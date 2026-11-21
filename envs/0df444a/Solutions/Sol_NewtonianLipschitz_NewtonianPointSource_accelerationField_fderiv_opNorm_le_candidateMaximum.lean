-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_opNorm_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:09:28.303173+00:00
-- url     : https://prove2.me/submissions/fb29a5b9-5b4a-4e25-a5fc-a39ec769b572

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    ‖fderiv ℝ c.accelerationField x‖ ≤
      (1 / ‖x‖ ^ 3) *
        (c.gravitationalParameter * candidateMaximum) := by
  have hfactor :
      0 ≤ (1 / ‖x‖ ^ 3) *
          (c.gravitationalParameter * candidateMaximum) :=
    mul_nonneg (by positivity)
      (mul_nonneg c.gravitationalParameter_nonneg
        candidateMaximum_nonneg)
  apply ContinuousLinearMap.opNorm_le_bound _ hfactor
  intro h
  exact c.accelerationField_fderiv_norm_le_candidateMaximum x h hx
end NewtonianPointSource
end NewtonianLipschitz
