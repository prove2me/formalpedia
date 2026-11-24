-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.iwahori_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:13:15.170481+00:00
-- url     : https://prove2.me/submissions/6cfc2fea-0e7e-4d49-b8ec-9cfca0fbfcf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Theorems.Thm_GlobalTheory_UnipotentBorder_udl_unique
import Theorems.Thm_GlobalTheory_UnipotentBorder_diag_unit
import Theorems.Thm_GlobalTheory_UnipotentBorder_udl_exists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] {n : ℕ} [IsLocalRing O] {α β : O}, ¬IsUnit β → ∀ (g : GL (Fin n) O), d2 α β (↑g : Matrix (Fin n) (Fin n) O) → ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O, d3 α (Prod.fst p) ∧ d1 β (Prod.snd (Prod.snd p)) ∧ (↑g : Matrix (Fin n) (Fin n) O) = (Prod.fst p * Matrix.diagonal fun (i : Fin n) ↦ (↑(Prod.fst (Prod.snd p) i) : O)) * Prod.snd (Prod.snd p)) := by
  dsimp only
  intro O _ n _ α β hβ g hg
  obtain ⟨U, D, L, hU, hL, hgeq⟩ := udl_exists hβ n (↑g : Matrix (Fin n) (Fin n) O) hg
    (fun i ↦ diag_unit hβ (↑g : Matrix (Fin n) (Fin n) O) (Matrix.isUnits_det_units g)
      (fun i j h ↦ (hg i j).2 h) i)
  refine ⟨(U, D, L), ⟨hU, hL, hgeq⟩, ?_⟩
  rintro ⟨U', D', L'⟩ ⟨hU', hL', hg'⟩
  obtain ⟨h1, h2, h3⟩ := udl_unique n U' U L' L D' D
    (fun i j ↦ ⟨(hU' i j).1, (hU' i j).2.1⟩) (fun i j ↦ ⟨(hU i j).1, (hU i j).2.1⟩)
    (fun i j ↦ ⟨(hL' i j).1, (hL' i j).2.1⟩) (fun i j ↦ ⟨(hL i j).1, (hL i j).2.1⟩)
    (hg'.symm.trans hgeq)
  rw [h1, h2, h3]
end GlobalTheory.UnipotentBorder
