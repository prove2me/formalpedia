-- Prove2me | solution 1 for Lean4LPD.PauliString.one_le_card_antiSites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:31.12182+00:00
-- url     : https://prove2.me/submissions/cd1b3a4d-2c4b-4060-b23f-3cc19cd870e3

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_card_antiSites

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : sympForm G s = 1) : 1 ≤ (antiSites G s).card := by
  rcases Nat.eq_zero_or_pos (antiSites G s).card with hz | hp
  · rw [sympForm_eq_card_antiSites, hz] at h
    exact absurd h (by decide)
  · exact hp
end Lean4LPD.PauliString
