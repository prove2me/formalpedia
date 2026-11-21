-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_rowSum_le_candidateMaximum_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:05:26.808491+00:00
-- url     : https://prove2.me/submissions/3a87081b-c9e3-4819-aee6-97cc3cc4484a

module
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_rowSum_le_candidateMaximum_norm
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
theorem _root_.solution
    (μ d : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hclear : d ≤ ‖x‖) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / d ^ 3) * (μ * candidateMaximum) := by
  have hnorm : 0 < ‖x‖ := lt_of_lt_of_le hd hclear
  have hx : x ≠ 0 := norm_pos_iff.mp hnorm
  have hpow : d ^ 3 ≤ ‖x‖ ^ 3 :=
    pow_le_pow_left₀ hd.le hclear 3
  have hinv : (1 : ℝ) / ‖x‖ ^ 3 ≤ 1 / d ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hnorm 3) (pow_pos hd 3)).2
    simpa only [one_mul] using hpow
  calc
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|)
      ≤ (1 / ‖x‖ ^ 3) * (μ * candidateMaximum) :=
        newtonianJacobianMatrix_rowSum_le_candidateMaximum_norm
          μ x i hμ hx
    _ ≤ (1 / d ^ 3) * (μ * candidateMaximum) :=
        mul_le_mul_of_nonneg_right hinv
          (mul_nonneg hμ candidateMaximum_nonneg)
end NewtonianLipschitz
