-- Prove2me | solution 1 for Lean4LPD.PauliString.layer_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:22.822789+00:00
-- url     : https://prove2.me/submissions/ddd4a898-0e31-4561-822d-bd1e44d73838

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_support_subset_cover
public import Theorems.Thm_Lean4LPD_PauliString_card_cover_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (hL : IsLayer kh L) (hkh : 1 ≤ kh) (hq : q ∈ oneLayer L p) :
    weight q ≤ kh * weight p :=
  le_trans (Finset.card_le_card (support_subset_cover hL.disjoint hq)) (card_cover_le hL hkh _)
end Lean4LPD.PauliString
