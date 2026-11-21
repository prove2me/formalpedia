-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:12:36.904003+00:00
-- url     : https://prove2.me/submissions/4b066ce4-1c80-4314-8223-0dd2e35646af

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorWitness
public import Definitions.Def_NewtonianLipschitz_ConvexBaseline
public import Definitions.Def_NewtonianLipschitz_ConvexSharp
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_contDiffAt
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_opNorm_le_clearance
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
    (c : NewtonianPointSource)
    (positions : Set Vec3) (hconvex : Convex ℝ positions)
    (d : ℝ) (hd : 0 < d)
    (hclear : ∀ z ∈ positions, d ≤ ‖z‖)
    (x y : Vec3) (hx : x ∈ positions) (hy : y ∈ positions) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)) *
        ‖x - y‖ := by
  have hnoncollision : ∀ z ∈ positions, z ≠ 0 := by
    intro z hz
    have hpos : 0 < ‖z‖ := lt_of_lt_of_le hd (hclear z hz)
    exact norm_pos_iff.mp hpos
  have hdiff : ∀ z ∈ positions,
      DifferentiableAt ℝ c.accelerationField z := by
    intro z hz
    exact (c.accelerationField_contDiffAt z
      (hnoncollision z hz)).differentiableAt_one
  have hbound : ∀ z ∈ positions,
      ‖fderiv ℝ c.accelerationField z‖ ≤
        (1 / d ^ 3) *
          (c.gravitationalParameter * candidateMaximum) := by
    intro z hz
    exact c.accelerationField_fderiv_opNorm_le_clearance
      z d hd (hclear z hz)
  have hmean :=
    hconvex.norm_image_sub_le_of_norm_fderiv_le
      hdiff hbound hx hy
  simpa only [dist_eq_norm, norm_sub_rev] using hmean
end NewtonianPointSource
end NewtonianLipschitz
