-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_lipschitzOnWith_of_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:00:25.245834+00:00
-- url     : https://prove2.me/submissions/a217eecf-8878-4b78-9d3a-5e2d80f52341

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexBaseline
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_clearanceLipschitzCoefficient_coe
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_contDiffAt
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_ten_of_clearance
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero


section
public section
open scoped NNReal Topology InnerProductSpace
namespace NewtonianLipschitz
private theorem no_collision_of_clearance
    (positions : Set Vec3) (d : ℝ) (hd : 0 < d)
    (hclear : ∀ x ∈ positions, d ≤ euclideanRadius x) :
    ∀ x ∈ positions, x ≠ 0 := by
  intro x hx hzero
  have hpos : 0 < euclideanRadius x :=
    lt_of_lt_of_le hd (hclear x hx)
  have hzeroRadius : euclideanRadius x = 0 := by
    rw [hzero, euclideanRadius_eq_physical_norm]
    simp
  exact (ne_of_gt hpos) hzeroRadius
end NewtonianLipschitz
end
end

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
      (NewtonianPointSource.clearanceLipschitzCoefficient d M hd)
      c.accelerationField positions := by
  have hnoncollision : ∀ x ∈ positions, x ≠ 0 :=
    no_collision_of_clearance positions d hd hclear
  have hdiff : ∀ x ∈ positions,
      DifferentiableAt ℝ c.accelerationField x := by
    intro x hx
    exact (c.accelerationField_contDiffAt x
      (hnoncollision x hx)).differentiableAt_one
  have hcoefficient_nonneg : 0 ≤ 10 * (M : ℝ) / d ^ 3 := by
    positivity
  have hbound : ∀ x ∈ positions,
      ‖fderiv ℝ c.accelerationField x‖ ≤
        10 * (M : ℝ) / d ^ 3 := by
    intro x hx
    apply ContinuousLinearMap.opNorm_le_bound _
      hcoefficient_nonneg
    intro h
    exact c.accelerationField_fderiv_norm_le_ten_of_clearance
      x h d (M : ℝ) (hnoncollision x hx) hd
      (hclear x hx) hM
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hmean :=
    hconvex.norm_image_sub_le_of_norm_fderiv_le
      hdiff hbound hx hy
  rw [NewtonianPointSource.clearanceLipschitzCoefficient_coe d M hd]
  simpa only [dist_eq_norm, norm_sub_rev] using hmean
end NewtonianPointSource
end NewtonianLipschitz
