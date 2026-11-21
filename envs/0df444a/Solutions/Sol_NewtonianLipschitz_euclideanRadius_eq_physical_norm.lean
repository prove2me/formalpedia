-- Prove2me | solution 1 for NewtonianLipschitz.euclideanRadius_eq_physical_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:21:47.770578+00:00
-- url     : https://prove2.me/submissions/5c1b35e3-52b1-4772-9a95-289b91ba47f1

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_coordinates
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (q : Vec3) :
    euclideanRadius q = ‖toPhysicalVec3 q‖ := by
  rw [euclideanRadius_eq_coordinates, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, toPhysicalVec3_apply, Real.norm_eq_abs, sq_abs]
end NewtonianLipschitz
