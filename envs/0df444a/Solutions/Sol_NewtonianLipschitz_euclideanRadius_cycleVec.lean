-- Prove2me | solution 1 for NewtonianLipschitz.euclideanRadius_cycleVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:46:58.209474+00:00
-- url     : https://prove2.me/submissions/860f2ef4-d2bf-4447-a8ab-1f9be6dfde52

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_coordinates
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero


attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) :
    euclideanRadius (cycleVec x) = euclideanRadius x := by
  rw [euclideanRadius_eq_coordinates (cycleVec x),
    euclideanRadius_eq_coordinates x]
  simp only [cycleVec_zero, cycleVec_one, cycleVec_two]
  congr 1
  ring
end NewtonianLipschitz
