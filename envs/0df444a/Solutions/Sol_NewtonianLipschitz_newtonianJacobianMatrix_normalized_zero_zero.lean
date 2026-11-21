-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:43:58.770509+00:00
-- url     : https://prove2.me/submissions/b96c47b4-14a3-47af-a0cf-3e41adc582a8

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_radius_sq
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero


attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two

set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 0 0 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (2 - u ^ 2 - v ^ 2) := by
  rw [newtonianJacobianMatrix_entry, normalizedVector_radius_sq]
  simp only [normalizedVector_zero, ite_true]
  ring
end NewtonianLipschitz
