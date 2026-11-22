-- Prove2me | solution 1 for Lean4LPD.PauliString.exists_commuting_weight_increase_by_full_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:22.459681+00:00
-- url     : https://prove2.me/submissions/f2c46ca5-a1e3-43ed-9aaa-9bad84bed116

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution :
    ∃ G s : PauliString 3,
      sympForm G s = 0 ∧ weight G = 2 ∧ weight s = 1 ∧ weight (G * s) = 3 :=
  ⟨⟨![1, 1, 0], 0, 0⟩, ⟨0, ![0, 0, 1], 0⟩, by decide, by decide, by decide, by decide⟩
end Lean4LPD.PauliString
