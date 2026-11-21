-- Prove2me | solution 2 for NewtonianLipschitz.newtonianJacobianMatrix_entry_abs_coordinateAbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:47:29.749935+00:00
-- url     : https://prove2.me/submissions/f1cb02d6-be09-4903-9b5a-596a4d7ecf52

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_coordinateAbs
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianNumerator_coordinateAbs
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
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
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    |newtonianJacobianMatrix μ (coordinateAbs x) i j| =
      |newtonianJacobianMatrix μ x i j| := by
  rw [newtonianJacobianMatrix_entry μ (coordinateAbs x) i j,
    newtonianJacobianMatrix_entry μ x i j,
    euclideanRadius_coordinateAbs]
  simp only [abs_mul]
  rw [newtonianJacobianNumerator_coordinateAbs]
end NewtonianLipschitz
