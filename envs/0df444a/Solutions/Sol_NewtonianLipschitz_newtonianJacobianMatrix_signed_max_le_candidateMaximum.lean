-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_signed_max_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:01:10.520426+00:00
-- url     : https://prove2.me/submissions/9acab887-0808-4c3b-96d3-fcae6f6e6e06

module
public import Definitions.Def_NewtonianLipschitz_JacobianAxisBounds
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_nonnegative_max_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_rowSum_coordinateAbs
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
    (μ : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ)
    (hmax :
      0 < max (|x 0|) (max (|x 1|) (|x 2|))) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (max (|x 0|) (max (|x 1|) (|x 2|))) ^ 3) *
        (μ * candidateMaximum) := by
  have h0 : 0 ≤ coordinateAbs x 0 := by
    rw [coordinateAbs_apply]
    exact abs_nonneg _
  have h1 : 0 ≤ coordinateAbs x 1 := by
    rw [coordinateAbs_apply]
    exact abs_nonneg _
  have h2 : 0 ≤ coordinateAbs x 2 := by
    rw [coordinateAbs_apply]
    exact abs_nonneg _
  have hmax' :
      0 < max (coordinateAbs x 0)
        (max (coordinateAbs x 1) (coordinateAbs x 2)) := by
    simpa only [coordinateAbs_apply] using hmax
  have hbound :=
    newtonianJacobianMatrix_nonnegative_max_le_candidateMaximum
      μ (coordinateAbs x) i hμ h0 h1 h2 hmax'
  calc
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|)
      = ∑ j : Fin 3,
          |newtonianJacobianMatrix μ (coordinateAbs x) i j| :=
        (newtonianJacobianMatrix_rowSum_coordinateAbs μ x i).symm
    _ ≤ (1 / (max (|x 0|) (max (|x 1|) (|x 2|))) ^ 3) *
          (μ * candidateMaximum) := by
        simpa only [coordinateAbs_apply] using hbound
end NewtonianLipschitz
