-- Prove2me | solution 1 for Lean4LPD.PauliString.card_antiLayer_powersetCard_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:02.666604+00:00
-- url     : https://prove2.me/submissions/7bb91125-65fd-4973-adb4-1ff0ebf1b703

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_card_antiLayer_le_weight

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) (j : ℕ) :
    ((antiLayer L p).powersetCard j).card ≤ (wt p).choose j := by
  rw [Finset.card_powersetCard]
  exact Nat.choose_le_choose j (card_antiLayer_le_weight L hL p)
end Lean4LPD.PauliString
