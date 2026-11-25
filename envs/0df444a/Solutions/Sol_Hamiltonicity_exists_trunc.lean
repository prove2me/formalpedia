-- Prove2me | solution 1 for Hamiltonicity.exists_trunc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:18:22.013793+00:00
-- url     : https://prove2.me/submissions/c3125cc8-19b5-453b-8be9-be71bc18e0c5

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
theorem _root_.solution {H : SimpleGraph V} (B : Set V) : ∀ {a b : V} (p : H.Walk a b), b ∈ B →
    p.IsPath → ∃ b' ∈ B, ∃ p' : H.Walk a b', p'.IsPath ∧ p'.support ⊆ p.support ∧
      ∀ y ∈ p'.support, y ∈ B → y = b'
  | _, _, .nil, hb, _ => ⟨_, hb, .nil, Walk.IsPath.nil, fun _ h => h, by simp⟩
  | a, _, .cons h q, hb, hp => by
    by_cases ha : a ∈ B
    · exact ⟨a, ha, .nil, Walk.IsPath.nil, by simp, by simp⟩
    · rw [Walk.cons_isPath_iff] at hp
      obtain ⟨b', hb', q', hq', hsub, hlast⟩ := solution B q hb hp.1
      refine ⟨b', hb', .cons h q', ?_, ?_, ?_⟩
      · rw [Walk.cons_isPath_iff]
        exact ⟨hq', fun h' => hp.2 (hsub h')⟩
      · simp only [Walk.support_cons]
        exact List.cons_subset_cons _ hsub
      · intro y hy hyB
        rw [Walk.support_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact absurd hyB ha
        · exact hlast y hy hyB
end Hamiltonicity
