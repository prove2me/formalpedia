-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:21.231253+00:00
-- url     : https://prove2.me/submissions/d18c1055-5beb-492b-bdf2-59bb109d46bc

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_card_cancelSites_add_card_antiSites_add_card_createSites
public import Theorems.Thm_Lean4LPD_PauliString_weight_mul_add_card_cancelSites

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (G s : PauliString n) : weight (G * s) ≤ weight s + weight G := by
  have hb := weight_mul_add_card_cancelSites G s
  have hp := card_cancelSites_add_card_antiSites_add_card_createSites G s
  omega
end Lean4LPD.PauliString
