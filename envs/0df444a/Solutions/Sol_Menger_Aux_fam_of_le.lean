-- Prove2me | solution 1 for Menger.Aux.fam_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:18:15.557136+00:00
-- url     : https://prove2.me/submissions/3d9bf817-75fd-4aa0-ab35-b5d3e365dabd

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Theorems.Thm_Menger_Aux_Fam_mono
public import Theorems.Thm_Menger_Aux_fam_base
public import Theorems.Thm_Menger_Aux_orient
public import Theorems.Thm_Menger_Aux_fam_step

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution [Finite V] (n : ℕ) : ∀ (G : SimpleGraph V), G.edgeSet.ncard = n →
    ∀ (A B : Finset V) (k : ℕ), (∀ X, Sep G A B X → k ≤ X.card) → Fam G A B k := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn A B k hk
  by_cases hG : ∀ x y, ¬ G.Adj x y
  · exact fam_base hG hk
  push Not at hG
  obtain ⟨x, y, hxy⟩ := hG
  have hlt : (G.deleteEdges {s(x, y)}).edgeSet.ncard < n := by
    rw [edgeSet_deleteEdges, ← hn]
    exact Set.ncard_sdiff_singleton_lt_of_mem hxy (Set.toFinite _)
  have IH := fun A' B' => ih _ hlt (G.deleteEdges {s(x, y)}) rfl A' B' k
  by_cases hall : ∀ X, Sep (G.deleteEdges {s(x, y)}) A B X → k ≤ X.card
  · exact (IH A B hall).mono (G.deleteEdges_le _)
  push Not at hall
  obtain ⟨Y, hY, hYk⟩ := hall
  have hGY : ¬ Sep G A B Y := fun h => absurd (hk Y h) (by omega)
  obtain ⟨x', y', hadj, he', hRx, hRy⟩ := orient hY hGY
  exact fam_step hadj he' hY hYk hk hRx hRy IH
end Menger.Aux
