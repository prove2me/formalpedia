-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_layerBlockTraj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:03:49.490307+00:00
-- url     : https://prove2.me/submissions/ff098534-aa10-4e40-b5e3-f71236001bdb

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (layers : ℕ → List (PauliString n × ℝ))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1)
    (O : Matrix (Bits n) (Bits n) ℂ) (i : ℕ) :
    pauliNorm (layerBlockTraj layers O i) = pauliNorm O := by
  induction i with
  | zero => rfl
  | succ i ih => rw [layerBlockTraj_succ, pauliNorm_layerConj _ (hherm i), ih]
end Lean4LPD.PauliString
