-- Prove2me | solution 1 for Lean4LPD.PauliString.layerAntiCount_le_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:46:48.143795+00:00
-- url     : https://prove2.me/submissions/24ece22f-2c9d-4fa4-a61d-f4a164845ccd

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_card_antiLayer_le_weight
public import Theorems.Thm_Lean4LPD_PauliString_layerAntiCount_eq_card_antiLayer

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) : layerAntiCount L p ≤ wt p := by
  rw [layerAntiCount_eq_card_antiLayer L hL]
  exact card_antiLayer_le_weight L hL p
end Lean4LPD.PauliString
