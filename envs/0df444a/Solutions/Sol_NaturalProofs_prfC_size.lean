-- Prove2me | solution 1 for NaturalProofs.prfC_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:20.414262+00:00
-- url     : https://prove2.me/submissions/4ca8546c-a134-45d9-a7fc-a047976e0095

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_walkC_size
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_size
public import Theorems.Thm_NaturalProofs_MCircuit_toCircuit_size
public import Theorems.Thm_NaturalProofs_MCircuit_wires_size


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (hk : 0 < k) (n : ℕ) (s : Bits k) :
    (prfC gc hk n s).size ≤ n * (2 * k * B + 4 * k) := by
  have := walkC_size gc hB (wires (fun j => .const (s j))) ((List.finRange n).map Sum.inl)
  simpa [prfC, toCircuit_size, mapOut_size, wires_size] using this
end NaturalProofs
