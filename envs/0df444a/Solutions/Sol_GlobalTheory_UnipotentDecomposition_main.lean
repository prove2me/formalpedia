-- Prove2me | solution 1 for GlobalTheory.UnipotentDecomposition.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:41.968837+00:00
-- url     : https://prove2.me/submissions/5286ed44-3d90-4297-b94f-9d3ab04311a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Theorems.Thm_GlobalTheory_UnipotentDecomposition_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentDecomposition
open Matrix
namespace GlobalTheory.UnipotentDecomposition
theorem _root_.solution : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] [IsLocalRing O] {α β : O}, ¬IsUnit (α * β) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), d2 α β g → (∀ (i : Fin n), IsUnit (g i i)) → ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O), d3 α u ∧ d1 β l ∧ g = (u * Matrix.diagonal fun (i : Fin n) ↦ (↑(d i) : O)) * l ∧ ∀ (i : Fin n), α * β ∣ (↑(d i) : O) - g i i) := by
  intro d1 d2 d3 O _ _ α β hab n g hg hu
  exact key hab n g hg hu
end GlobalTheory.UnipotentDecomposition
