-- Prove2me | solution 2 for Menger.card_le_of_separates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:49:22.6751+00:00
-- url     : https://prove2.me/submissions/bd7c70d7-4603-49e5-9ed6-7e45337a6293

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Definitions.Def_MengerHamilton_Menger

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger
variable {V : Type*}
namespace Menger
theorem _root_.solution {G : SimpleGraph V} {A B X : Finset V}
    (hX : Separates G A B X) {m : ℕ} (a b : Fin m → V) (p : ∀ i, G.Walk (a i) (b i))
    (hA : ∀ i, a i ∈ A) (hB : ∀ i, b i ∈ B)
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support) :
    m ≤ X.card := by
  classical
  have h : ∀ i, ∃ x ∈ X, x ∈ (p i).support := fun i => hX _ (hA i) _ (hB i) (p i)
  choose f hfX hfp using h
  have hinj : Set.InjOn f ((Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro i _ j _ hij
    by_contra hne
    exact hdisj i j hne _ (hfp i) (by rw [hij]; exact hfp j)
  simpa using Finset.card_le_card_of_injOn f (fun i _ => hfX i) hinj
end Menger
