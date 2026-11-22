-- Prove2me | solution 1 for Lean4LPD.PauliString.pauli_rotation_branch_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:47.469821+00:00
-- url     : https://prove2.me/submissions/609939a0-1e76-43cb-bd53-33f230b2cfb0

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s : PauliString n} {θ : ℝ} {kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (hG : IsSelfAdjoint G) (h : sympForm G s = 1) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
      = (Real.cos θ : ℂ) • toMatrix s + (Complex.I * Real.sin θ) • toMatrix (G * s) := by
  rw [pauli_rotation_branch hG s θ, if_neg (by rw [h]; decide)]
end Lean4LPD.PauliString
