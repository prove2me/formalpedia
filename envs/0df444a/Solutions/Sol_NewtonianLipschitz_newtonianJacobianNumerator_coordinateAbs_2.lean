-- Prove2me | solution 2 for NewtonianLipschitz.newtonianJacobianNumerator_coordinateAbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:45:55.104217+00:00
-- url     : https://prove2.me/submissions/40a6c4a9-9974-4500-ae4a-bf8da832a407

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
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
theorem _root_.solution (x : Vec3)
    (i j : Fin 3) :
    |3 * coordinateAbs x i * coordinateAbs x j -
      euclideanRadius x ^ 2 * (if i = j then 1 else 0)| =
    |3 * x i * x j -
      euclideanRadius x ^ 2 * (if i = j then 1 else 0)| := by
  simp only [coordinateAbs_apply]
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl, mul_one]
    have hsq : (3 : ℝ) * |x i| * |x i| =
        3 * x i * x i := by
      nlinarith [sq_abs (x i)]
    rw [hsq]
  · simp only [if_neg hij, mul_zero, sub_zero, abs_mul, abs_abs]
end NewtonianLipschitz
