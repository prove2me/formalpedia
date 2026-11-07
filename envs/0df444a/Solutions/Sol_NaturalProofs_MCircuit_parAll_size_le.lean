-- Prove2me | solution 1 for NaturalProofs.MCircuit.parAll_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:38:22.416247+00:00
-- url     : https://prove2.me/submissions/1017d9b6-0550-4013-a5dc-60f8f454222a

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_MCircuit_par_size_le

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit
namespace NaturalProofs.MCircuit
theorem _root_.solution [Fintype α] [DecidableEq α] (E : α → MCircuit β Unit) (B : ℕ)
    (hE : ∀ a, (E a).size ≤ B) : (parAll E).size ≤ Fintype.card α * B := by
  have := par_size_le E (Finset.univ : Finset α).toList B hE
  rw [Finset.length_toList, Finset.card_univ] at this
  exact this
end NaturalProofs.MCircuit
