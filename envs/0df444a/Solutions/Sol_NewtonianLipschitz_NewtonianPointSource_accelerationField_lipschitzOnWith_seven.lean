-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_lipschitzOnWith_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:05:07.173146+00:00
-- url     : https://prove2.me/submissions/642a8fd8-b903-43f9-b96e-40e2b47dc829

module
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexImproved
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_sevenLipschitzCoefficient_coe
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_contDiffAt
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_seven_of_clearance
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (positions : Set Vec3)
    (hconvex : Convex ℝ positions)
    (d : ℝ) (M : ℝ≥0) (hd : 0 < d)
    (hclear : ∀ x ∈ positions, d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ (M : ℝ)) :
    LipschitzOnWith
      (NewtonianPointSource.sevenLipschitzCoefficient d M hd)
      c.accelerationField positions := by
  have hnoncollision : ∀ x ∈ positions, x ≠ 0 := by
    intro x hx hzero
    have hpos : 0 < euclideanRadius x :=
      lt_of_lt_of_le hd (hclear x hx)
    have hzeroRadius : euclideanRadius x = 0 := by
      rw [hzero, euclideanRadius_eq_physical_norm]
      simp
    exact (ne_of_gt hpos) hzeroRadius
  have hdiff : ∀ x ∈ positions,
      DifferentiableAt ℝ c.accelerationField x := by
    intro x hx
    exact (c.accelerationField_contDiffAt x
      (hnoncollision x hx)).differentiableAt_one
  have hnonneg : 0 ≤ 7 * (M : ℝ) / d ^ 3 := by positivity
  have hbound : ∀ x ∈ positions,
      ‖fderiv ℝ c.accelerationField x‖ ≤
        7 * (M : ℝ) / d ^ 3 := by
    intro x hx
    apply ContinuousLinearMap.opNorm_le_bound _ hnonneg
    intro h
    exact c.accelerationField_fderiv_norm_le_seven_of_clearance
      x h d (M : ℝ) (hnoncollision x hx) hd (hclear x hx) hM
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hmean :=
    hconvex.norm_image_sub_le_of_norm_fderiv_le
      hdiff hbound hx hy
  rw [NewtonianPointSource.sevenLipschitzCoefficient_coe d M hd]
  simpa only [dist_eq_norm, norm_sub_rev] using hmean
end NewtonianPointSource
end NewtonianLipschitz
