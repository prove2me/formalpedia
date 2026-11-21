-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_common_face
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:14:16.663965+00:00
-- url     : https://prove2.me/submissions/36f7a8e1-91a2-467b-949a-2fb6f446c8c9

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
public import Theorems.Thm_NewtonianLipschitz_cartesianPositiveSafeHalfspace_convex
public import Theorems.Thm_NewtonianLipschitz_cartesianPositiveSafeHalfspace_clearance
public import Theorems.Thm_NewtonianLipschitz_cartesianNegativeSafeHalfspace_convex
public import Theorems.Thm_NewtonianLipschitz_cartesianNegativeSafeHalfspace_clearance
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_convex
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
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ)
    (hd : 0 < d)
    (hface : ∃ i : Fin 3,
      (d ≤ x i ∧ d ≤ y i) ∨
      (x i ≤ -d ∧ y i ≤ -d)) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)) *
        ‖x - y‖ := by
  obtain ⟨i, hpos | hneg⟩ := hface
  · let positions : Set Vec3 := {z | d ≤ z i}
    have hconvex : Convex ℝ positions := by
      simpa only [positions] using cartesianPositiveSafeHalfspace_convex i d
    have hclear : ∀ z ∈ positions, d ≤ ‖z‖ := by
      intro z hz
      exact cartesianPositiveSafeHalfspace_clearance i d z hz
    exact c.accelerationField_norm_sub_le_candidateMaximum_convex
      positions hconvex d hd hclear x y hpos.1 hpos.2
  · let positions : Set Vec3 := {z | z i ≤ -d}
    have hconvex : Convex ℝ positions := by
      simpa only [positions] using cartesianNegativeSafeHalfspace_convex i d
    have hclear : ∀ z ∈ positions, d ≤ ‖z‖ := by
      intro z hz
      exact cartesianNegativeSafeHalfspace_clearance i d z hz
    exact c.accelerationField_norm_sub_le_candidateMaximum_convex
      positions hconvex d hd hclear x y hneg.1 hneg.2
end NewtonianPointSource
end NewtonianLipschitz
