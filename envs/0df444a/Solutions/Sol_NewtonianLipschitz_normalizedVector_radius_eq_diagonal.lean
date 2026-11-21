-- Prove2me | solution 1 for NewtonianLipschitz.normalizedVector_radius_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:44:15.410989+00:00
-- url     : https://prove2.me/submissions/1c0f99bc-e3d4-4d78-91a2-226b9cd9a721

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Theorems.Thm_NewtonianLipschitz_diagonalParameter_sq
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_coordinates
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



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (u v : ℝ) :
    euclideanRadius (normalizedVector u v) =
      Real.sqrt (1 + 2 * (diagonalParameter u v) ^ 2) := by
  obtain ⟨ht0, hsq⟩ := diagonalParameter_sq u v
  rw [euclideanRadius_eq_coordinates]
  simp only [normalizedVector_zero, normalizedVector_one, normalizedVector_two]
  change Real.sqrt ((1 : ℝ) ^ 2 + u ^ 2 + v ^ 2) =
    Real.sqrt (1 + 2 * (diagonalParameter u v) ^ 2)
  congr 1
  nlinarith [hsq]
end NewtonianLipschitz
