-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_two_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:45:34.109652+00:00
-- url     : https://prove2.me/submissions/eb524e69-5dce-4707-b30f-505cb886cc23

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 2 0 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (3 * v) := by
  rw [newtonianJacobianMatrix_entry]
  norm_num [Fin.ext_iff, normalizedVector_zero, normalizedVector_one, normalizedVector_two] <;> ring
end NewtonianLipschitz
