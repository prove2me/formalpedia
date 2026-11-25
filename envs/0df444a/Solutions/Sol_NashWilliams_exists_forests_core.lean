-- Prove2me | solution 1 for NashWilliams.exists_forests_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:22:45.950032+00:00
-- url     : https://prove2.me/submissions/bfd06dad-4a28-4c7c-994d-d9004255af64

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_reachable_map_of_adj
public import Theorems.Thm_NashWilliams_exchGraph_adj
public import Theorems.Thm_NashWilliams_reach_uncov_reachable
public import Theorems.Thm_NashWilliams_reach_reachable_iff

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
namespace NashWilliams
theorem _root_.solution [Finite V] (G : SimpleGraph V) (k : ℕ) :
    ∃ (F : Fin k → SimpleGraph V) (H : SimpleGraph V), (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧
      (Pairwise fun i j ↦ Disjoint (F i) (F j)) ∧ H ≤ G ∧
      (∀ i a b, H.Reachable a b → (F i ⊓ H).Reachable a b) ∧
      (∀ a b, G.Adj a b → ¬ H.Adj a b → ∃ i, (F i).Adj a b) := by
  have : Finite (SimpleGraph V) := Finite.of_injective _ fun _ _ h ↦ SimpleGraph.ext h
  have hval0 : Valid G (fun _ : Fin k ↦ (⊥ : SimpleGraph V)) :=
    ⟨fun _ ↦ ⟨bot_le, isAcyclic_bot⟩, fun _ _ _ ↦ disjoint_bot_left⟩
  obtain ⟨F₀, hF₀, hmax⟩ := Set.exists_max_image {F : Fin k → SimpleGraph V | Valid G F} total
    (Set.toFinite _) ⟨_, hval0⟩
  refine ⟨F₀, exchGraph G F₀, hF₀.1, hF₀.2, fun a b h ↦ ?_, fun i a b hab ↦ ?_,
    fun a b hab hH ↦ ?_⟩
  · obtain ⟨_, _, hu⟩ := exchGraph_adj.1 h
    exact hu.1
  · refine reachable_map_of_adj id (fun c d h ↦ ?_) hab
    obtain ⟨F, hF, hu⟩ := exchGraph_adj.1 h
    exact (reach_reachable_iff hF₀ hmax hF i c d).1 (reach_uncov_reachable hF₀ hmax hF hu i)
  · by_contra h
    exact hH (exchGraph_adj.2 ⟨F₀, .refl, hab, fun j hj ↦ h ⟨j, hj⟩⟩)
end NashWilliams
