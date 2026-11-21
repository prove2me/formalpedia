-- Prove2me | solution 1 for NewtonianLipschitz.criticalDiagonal_outward_ray_cartesian_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:55:06.3875+00:00
-- url     : https://prove2.me/submissions/d53f95d1-4694-4d53-817f-19ce9cf3863a

module
public import Definitions.Def_NewtonianLipschitz_DerivativeAttainingDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
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
    (h : Vec3) (hfirst : 0 ≤ h 0)
    (s : ℝ) (hs : 0 ≤ s) :
    (1 : ℝ) ≤
      ‖normalizedVector candidateCriticalPoint candidateCriticalPoint +
        s • h‖ := by
  let z := normalizedVector candidateCriticalPoint candidateCriticalPoint +
    s • h
  have hnonneg : 0 ≤ s * h 0 := mul_nonneg hs hfirst
  have hcoord : (1 : ℝ) ≤ z 0 := by
    change (1 : ℝ) ≤
      (normalizedVector candidateCriticalPoint candidateCriticalPoint) 0 +
        s * h 0
    rw [normalizedVector_zero]
    linarith
  have habs : z 0 ≤ |z 0| := le_abs_self _
  have hle : |z 0| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm z 0)
  exact hcoord.trans (habs.trans hle)
end NewtonianLipschitz
