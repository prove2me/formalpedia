-- Prove2me | solution 1 for Lean4LPD.PauliString.rot_toMatrix_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:28.765813+00:00
-- url     : https://prove2.me/submissions/737a2407-1e64-438c-87ce-d253170b5809

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Theorems.Thm_Lean4LPD_PauliString_star_toMatrix_of_isSelfAdjoint
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_self_of_isSelfAdjoint
public import Theorems.Thm_Lean4LPD_rot_mem_unitary


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s : PauliString n} {θ : ℝ} {kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (hG : IsSelfAdjoint G) (θ : ℝ) :
    rot (toMatrix G) θ ∈ unitary (Matrix (Bits n) (Bits n) ℂ) :=
  rot_mem_unitary (toMatrix_mul_self_of_isSelfAdjoint hG) (star_toMatrix_of_isSelfAdjoint hG)
end Lean4LPD.PauliString
