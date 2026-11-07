-- Prove2me | solution 1 for NaturalProofs.stepC_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:12.39864+00:00
-- url     : https://prove2.me/submissions/84d0f230-d374-4cef-af9c-ae54d4eaa470

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_genC_eval
public import Theorems.Thm_NaturalProofs_muxC_eval
public import Theorems.Thm_NaturalProofs_MCircuit_extend_eval
public import Theorems.Thm_NaturalProofs_MCircuit_mapIn_eval
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_eval
public import Theorems.Thm_NaturalProofs_MCircuit_parAll_eval


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (s : β ⊕ Bool)
    (Cv : MCircuit β (Fin k)) (x : β → Bool) :
    (stepC gc s Cv).eval x = half (bitval x s) (G k (Cv.eval x)) := by
  funext j
  simp only [stepC, mapOut_eval, extend_eval, Sum.elim_inr, Sum.elim_inl, parAll_eval,
    muxC_eval, mapIn_eval, Sum.elim_comp_inr, genC_eval G gc hgc, half]
  rcases s with b | b
  · cases h : x b <;> simp [bitval, h]
  · cases b <;> simp [bitval]
end NaturalProofs
