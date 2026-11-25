-- Prove2me | solution 2 for Hamiltonicity.exists_path_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:47:16.797993+00:00
-- url     : https://prove2.me/submissions/083a0aec-e933-4dbd-ba81-f9e6e782df1f

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution {G : SimpleGraph V} (S : Set V) (hS : (G.induce Sᶜ).Connected)
    {a b : V} (ha : a ∉ S) (hb : b ∉ S) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ y ∈ p.support, y ∉ S := by
  classical
  obtain ⟨w⟩ := hS.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨(w.map (Embedding.induce Sᶜ).toHom).bypass, Walk.bypass_isPath _, fun y hy => ?_⟩
  have := Walk.support_bypass_subset_support _ hy
  erw [Walk.support_map, List.mem_map] at this
  obtain ⟨z, -, rfl⟩ := this
  exact z.2
end Hamiltonicity
