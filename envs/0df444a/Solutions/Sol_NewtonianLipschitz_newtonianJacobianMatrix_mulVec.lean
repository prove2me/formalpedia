-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:43:29.493457+00:00
-- url     : https://prove2.me/submissions/b6c370ba-f95b-4ddf-b708-937be4d11f4a

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_eq_continuousLinearEquiv
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ : ℝ) (x h : Vec3) (hx : x ≠ 0) :
    newtonianJacobianMatrix μ x *ᵥ h =
      (-(μ) / euclideanRadius x ^ 3) • h +
        ((3 * μ / euclideanRadius x ^ 5) * (x ⬝ᵥ h)) • x := by
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
  have houter :
      (Matrix.vecMulVec x x) *ᵥ h =
        (x ⬝ᵥ h) • x := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
      Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [newtonianJacobianMatrix,
    Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, houter]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hr] <;> ring
end NewtonianLipschitz
