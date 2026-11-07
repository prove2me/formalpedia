-- Prove2me | solution 1 for NaturalProofs.genC_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:41:17.124578+00:00
-- url     : https://prove2.me/submissions/8e449d2c-af2a-4d0e-9f06-d084740f480f

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_MCircuit_parAll_size_le


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution (k B : ℕ) (hB : ∀ j, (gc k j).size ≤ B) : (genC gc k).size ≤ 2 * k * B := by
  have := parAll_size_le (fun j => ofCircuit (gc k j)) B (fun j => hB j)
  simpa [genC] using this
end NaturalProofs
