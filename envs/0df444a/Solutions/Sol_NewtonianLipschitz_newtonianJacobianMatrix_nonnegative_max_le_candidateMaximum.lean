-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_nonnegative_max_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:58:59.472956+00:00
-- url     : https://prove2.me/submissions/085acdf0-b083-4979-9d78-04c90da0e93f

module
public import Definitions.Def_NewtonianLipschitz_JacobianAxisBounds
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_firstMax_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_secondMax_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_thirdMax_le_candidateMaximum
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
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2)
    (hmax : 0 < max (x 0) (max (x 1) (x 2))) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (max (x 0) (max (x 1) (x 2))) ^ 3) *
        (μ * candidateMaximum) := by
  rcases le_total (x 1) (x 0) with h10 | h01
  · rcases le_total (x 2) (x 0) with h20 | h02
    · have hm :
          max (x 0) (max (x 1) (x 2)) = x 0 := by
        exact max_eq_left (max_le h10 h20)
      have hx0 : 0 < x 0 := by
        simpa only [hm] using hmax
      simpa only [hm] using
        (newtonianJacobianMatrix_firstMax_le_candidateMaximum
          μ x i hμ hx0 h1 h10 h2 h20)
    · have h12 : x 1 ≤ x 2 := le_trans h10 h02
      have hm :
          max (x 0) (max (x 1) (x 2)) = x 2 := by
        rw [max_eq_right h12, max_eq_right h02]
      have hx2 : 0 < x 2 := by
        simpa only [hm] using hmax
      simpa only [hm] using
        (newtonianJacobianMatrix_thirdMax_le_candidateMaximum
          μ x i hμ hx2 h0 h02 h1 h12)
  · rcases le_total (x 2) (x 1) with h21 | h12
    · have hm :
          max (x 0) (max (x 1) (x 2)) = x 1 := by
        rw [max_eq_left h21, max_eq_right h01]
      have hx1 : 0 < x 1 := by
        simpa only [hm] using hmax
      simpa only [hm] using
        (newtonianJacobianMatrix_secondMax_le_candidateMaximum
          μ x i hμ hx1 h0 h01 h2 h21)
    · have h02 : x 0 ≤ x 2 := le_trans h01 h12
      have hm :
          max (x 0) (max (x 1) (x 2)) = x 2 := by
        rw [max_eq_right h12, max_eq_right h02]
      have hx2 : 0 < x 2 := by
        simpa only [hm] using hmax
      simpa only [hm] using
        (newtonianJacobianMatrix_thirdMax_le_candidateMaximum
          μ x i hμ hx2 h0 h02 h1 h12)
end NewtonianLipschitz
