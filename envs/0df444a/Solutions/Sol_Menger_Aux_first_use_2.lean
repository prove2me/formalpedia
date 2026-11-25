-- Prove2me | solution 2 for Menger.Aux.first_use
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:48:45.340514+00:00
-- url     : https://prove2.me/submissions/c7651365-b35d-4d0f-bf8f-bd194f8adb18

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Theorems.Thm_Menger_Aux_R_of_mem
public import Theorems.Thm_Menger_Aux_R_disj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {G : SimpleGraph V} {e : Sym2 V} {A B Y : Finset V}
    (hY : Sep (G.deleteEdges {e}) A B Y) :
    ∀ {u b : V} (q : G.Walk u b), b ∈ B → R (G.deleteEdges {e}) A Y u →
      (∀ w ∈ q.support, w ∉ Y) →
      ∃ z w, G.Adj z w ∧ s(z, w) = e ∧ R (G.deleteEdges {e}) A Y z := by
  intro u b q
  induction q with
  | nil =>
    intro hb hR hq
    exact (R_disj hY hR (R.of_mem hb (hq _ (Walk.start_mem_support _)))).elim
  | @cons u w b' h q ih =>
    intro hb hR hq
    by_cases hs : s(u, w) = e
    · exact ⟨u, w, h, hs, hR⟩
    · apply ih hb ?_ (fun x hx => hq x (by simp [hx]))
      obtain ⟨a, ha, r, hr⟩ := hR
      have hadj : (G.deleteEdges {e}).Adj u w := by simp [h, hs]
      refine ⟨a, ha, r.concat hadj, fun x hx => ?_⟩
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hr x hx
      · exact hq x (by simp)
end Menger.Aux
