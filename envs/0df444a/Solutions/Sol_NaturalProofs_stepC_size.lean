-- Prove2me | solution 1 for NaturalProofs.stepC_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:35.87949+00:00
-- url     : https://prove2.me/submissions/9537a9e8-b2bd-4731-9bcb-aa235fd4e4fd

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_genC_size
public import Theorems.Thm_NaturalProofs_MCircuit_extend_size
public import Theorems.Thm_NaturalProofs_MCircuit_mapIn_size
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_size
public import Theorems.Thm_NaturalProofs_MCircuit_parAll_size_le


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (s : β ⊕ Bool)
    (Cv : MCircuit β (Fin k)) : (stepC gc s Cv).size ≤ Cv.size + (2 * k * B + 4 * k) := by
  have h1 := genC_size gc k B hB
  have h2 := parAll_size_le (muxC k s) 4 (fun j => le_refl _)
  simp only [stepC, mapOut_size, extend_size, mapIn_size, Fintype.card_fin] at h2 ⊢
  omega
end NaturalProofs
