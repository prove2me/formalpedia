-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_cauchy_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:56:54.32175+00:00
-- url     : https://prove2.me/submissions/a332dd37-136e-43cb-a88e-efd0a58f5a54

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_of_clearance

set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x h : Vec3) (d M : ℝ)
    (hx : x ≠ 0) (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      (M / d ^ 3) * ‖h‖ +
        (3 * M / d ^ 5) *
          (‖toPhysicalVec3 x‖ * ‖toPhysicalVec3 h‖) * ‖x‖ := by
  have hMnonneg : 0 ≤ M :=
    le_trans c.gravitationalParameter_nonneg hM
  have hcoef : 0 ≤ 3 * M / d ^ 5 := by
    positivity
  have hCS :
      abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) ≤
        ‖toPhysicalVec3 x‖ * ‖toPhysicalVec3 h‖ :=
    abs_real_inner_le_norm _ _
  have hterm :
      (3 * M / d ^ 5) *
          abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) * ‖x‖ ≤
        (3 * M / d ^ 5) *
          (‖toPhysicalVec3 x‖ * ‖toPhysicalVec3 h‖) * ‖x‖ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCS hcoef) (norm_nonneg x)
  exact
    (c.accelerationField_fderiv_norm_le_of_clearance x h d M
      hx hd hclear hM).trans (add_le_add (le_refl _) hterm)
end NewtonianPointSource
end NewtonianLipschitz
