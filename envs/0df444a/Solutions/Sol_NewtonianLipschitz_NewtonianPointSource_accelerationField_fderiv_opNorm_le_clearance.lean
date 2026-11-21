-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_opNorm_le_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:10:56.993913+00:00
-- url     : https://prove2.me/submissions/51db4a16-3bee-4140-8d82-186b44287191

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_opNorm_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) (d : ℝ)
    (hd : 0 < d) (hclear : d ≤ ‖x‖) :
    ‖fderiv ℝ c.accelerationField x‖ ≤
      (1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum) := by
  have hnorm : 0 < ‖x‖ := lt_of_lt_of_le hd hclear
  have hx : x ≠ 0 := norm_pos_iff.mp hnorm
  have hpow : d ^ 3 ≤ ‖x‖ ^ 3 :=
    pow_le_pow_left₀ hd.le hclear 3
  have hinv : (1 : ℝ) / ‖x‖ ^ 3 ≤ 1 / d ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hnorm 3) (pow_pos hd 3)).2
    simpa only [one_mul] using hpow
  calc
    ‖fderiv ℝ c.accelerationField x‖
      ≤ (1 / ‖x‖ ^ 3) *
          (c.gravitationalParameter * candidateMaximum) :=
        c.accelerationField_fderiv_opNorm_le_candidateMaximum x hx
    _ ≤ (1 / d ^ 3) *
          (c.gravitationalParameter * candidateMaximum) :=
        mul_le_mul_of_nonneg_right hinv
          (mul_nonneg c.gravitationalParameter_nonneg
            candidateMaximum_nonneg)
end NewtonianPointSource
end NewtonianLipschitz
