-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_entry_positive_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:48:10.758176+00:00
-- url     : https://prove2.me/submissions/0d6acb86-74cf-4eb0-a95c-fe672f2c3c82

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_smul
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_eq_continuousLinearEquiv
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero


attribute [local simp] NewtonianLipschitz.coordinateAbs_apply

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ c : ℝ) (x : Vec3) (i j : Fin 3)
    (hc : 0 < c) (hx : x ≠ 0) :
    newtonianJacobianMatrix μ (c • x) i j =
      (1 / c ^ 3) * newtonianJacobianMatrix μ x i j := by
  let e : Vec3 ≃L[ℝ] PhysicalVec3 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hphys : e x ≠ 0 := by
    intro hz
    apply hx
    apply e.injective
    simpa only [map_zero] using hz
  have hr : euclideanRadius x ≠ 0 := by
    rw [euclideanRadius_eq_physical_norm,
      toPhysicalVec3_eq_continuousLinearEquiv]
    exact norm_ne_zero_iff.mpr hphys
  rw [newtonianJacobianMatrix_entry μ (c • x) i j,
    newtonianJacobianMatrix_entry μ x i j,
    euclideanRadius_smul, abs_of_pos hc]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hc, hr] <;> ring
end NewtonianLipschitz
