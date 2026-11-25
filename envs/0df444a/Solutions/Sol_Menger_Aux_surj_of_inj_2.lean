-- Prove2me | solution 2 for Menger.Aux.surj_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:48:54.594062+00:00
-- url     : https://prove2.me/submissions/f0fede0d-6019-4e53-8829-db66f0520db0

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {k : ℕ} {X : Finset V} (f : Fin k → V) (hf : ∀ i, f i ∈ X)
    (hinj : Function.Injective f) (hc : X.card ≤ k) : ∀ v ∈ X, ∃ i, f i = v := by
  classical
  have hsub : Finset.univ.image f ⊆ X := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    exact hf i
  have hcard : X.card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact hc
  have := Finset.eq_of_subset_of_card_le hsub hcard
  intro v hv
  rw [← this] at hv
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
  exact ⟨i, hi⟩
end Menger.Aux
