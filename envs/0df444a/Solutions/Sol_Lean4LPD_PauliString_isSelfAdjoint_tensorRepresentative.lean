-- Prove2me | solution 1 for Lean4LPD.PauliString.isSelfAdjoint_tensorRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:03.023055+00:00
-- url     : https://prove2.me/submissions/021eb19c-9d08-4ea9-adde-3f768590e198

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
public import Theorems.Thm_Lean4LPD_PauliString_two_mul_yPhase
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset
namespace Lean4LPD.PauliString
theorem _root_.solution {n : ℕ} (p : PauliIndex n) :
    IsSelfAdjoint (tensorRepresentative p) := by
  apply isSelfAdjoint_iff_phase.2
  exact (two_mul_yPhase p.1 p.2).symm
end Lean4LPD.PauliString
