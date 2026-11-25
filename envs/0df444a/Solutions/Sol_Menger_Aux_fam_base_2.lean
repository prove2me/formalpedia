-- Prove2me | solution 2 for Menger.Aux.fam_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:48:18.555859+00:00
-- url     : https://prove2.me/submissions/a15f781d-9acf-4af2-a262-0297ae69be4a

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
theorem _root_.solution {G : SimpleGraph V} (hG : ∀ x y, ¬ G.Adj x y) {A B : Finset V} {k : ℕ}
    (hk : ∀ X, Sep G A B X → k ≤ X.card) : Fam G A B k := by
  classical
  have hsep : Sep G A B (A ∩ B) := by
    intro a ha b hb p
    cases p with
    | nil => exact ⟨a, Finset.mem_inter.2 ⟨ha, hb⟩, Walk.start_mem_support _⟩
    | cons h _ => exact absurd h (hG _ _)
  have hkc := hk _ hsep
  obtain ⟨f⟩ : Nonempty (Fin k ↪ (A ∩ B : Finset V)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hkc)
  refine ⟨fun i => ⟨f i, f i, Walk.nil⟩, fun i => ?_, fun i j hij => ?_⟩
  · have := (f i).2
    rw [Finset.mem_inter] at this
    refine ⟨this.1, this.2, Walk.IsPath.nil, ?_, ?_⟩ <;> simp
  · simp only [Walk.support_nil, List.mem_singleton]
    rintro w rfl h
    exact hij (f.injective (Subtype.ext h))
end Menger.Aux
