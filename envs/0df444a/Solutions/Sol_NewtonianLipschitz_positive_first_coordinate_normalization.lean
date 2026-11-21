-- Prove2me | solution 1 for NewtonianLipschitz.positive_first_coordinate_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:34:35.450893+00:00
-- url     : https://prove2.me/submissions/fdc610c1-d6a8-44bf-9d8f-c37e7e5c210f

module
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
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
    (x : Vec3) (hx0 : 0 < x 0) :
    (x 0) • normalizedVector (x 1 / x 0) (x 2 / x 0) = x := by
  have hfirst :
      ((x 0) • normalizedVector (x 1 / x 0) (x 2 / x 0)) 0 =
        x 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, normalizedVector_zero]
    ring
  have hsecond :
      ((x 0) • normalizedVector (x 1 / x 0) (x 2 / x 0)) 1 =
        x 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, normalizedVector_one]
    field_simp [ne_of_gt hx0] <;> ring
  have hthird :
      ((x 0) • normalizedVector (x 1 / x 0) (x 2 / x 0)) 2 =
        x 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, normalizedVector_two]
    field_simp [ne_of_gt hx0] <;> ring
  ext i
  fin_cases i
  · simpa using hfirst
  · simpa using hsecond
  · simpa using hthird
end NewtonianLipschitz
