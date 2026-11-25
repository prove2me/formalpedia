-- Prove2me | solution 1 for Menger.Aux.sep_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:09:49.277739+00:00
-- url     : https://prove2.me/submissions/5a0035d3-443b-442d-92bb-ed46f56caac9

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
theorem _root_.solution [DecidableEq V] {G : SimpleGraph V} {e : Sym2 V} {x y : V} (he : s(x, y) = e)
    {A B Y Z : Finset V} (hY : Sep (G.deleteEdges {e}) A B Y)
    (hy : ¬ R (G.deleteEdges {e}) A Y y)
    (hZ : Sep (G.deleteEdges {e}) A (insert x Y) Z) : Sep G A B Z := by
  have key : ∀ {u b : V} (q : G.Walk u b), b ∈ B → (∀ w ∈ q.support, w ∉ Z) →
      (∃ a ∈ A, ∃ r : (G.deleteEdges {e}).Walk a u, ∀ w ∈ r.support, w ∉ Z ∧ w ∉ insert x Y) →
      False := by
    intro u b q
    induction q with
    | nil =>
      rintro hb - ⟨a, ha, r, hr⟩
      obtain ⟨v, hv, hvr⟩ := hY a ha _ hb r
      exact (hr v hvr).2 (Finset.mem_insert_of_mem hv)
    | @cons u w b h q ih =>
      rintro hb hq ⟨a, ha, r, hr⟩
      have huX := (hr u r.end_mem_support).2
      have hwZ : w ∉ Z := hq w (by simp)
      by_cases hs : s(u, w) = e
      · rw [← he, Sym2.eq_iff] at hs
        rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact huX (h1 ▸ Finset.mem_insert_self _ _)
        · subst h1
          exact hy ⟨a, ha, r, fun v hv hvY => (hr v hv).2 (Finset.mem_insert_of_mem hvY)⟩
      · have hadj : (G.deleteEdges {e}).Adj u w := by simp [h, hs]
        by_cases hwX : w ∈ insert x Y
        · obtain ⟨z, hz, hzr⟩ := hZ a ha w hwX (r.concat hadj)
          rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hzr
          rcases hzr with hzr | rfl
          · exact (hr z hzr).1 hz
          · exact hwZ hz
        · refine ih hb (fun v hv => hq v (by simp [hv])) ⟨a, ha, r.concat hadj, fun v hv => ?_⟩
          rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact hr v hv
          · exact ⟨hwZ, hwX⟩
  intro a ha b hb p
  by_contra hcon
  push Not at hcon
  have hp : ∀ w ∈ p.support, w ∉ Z := fun w hw hwZ => hcon w hwZ hw
  by_cases haX : a ∈ insert x Y
  · obtain ⟨z, hz, hzs⟩ := hZ a ha a haX Walk.nil
    simp only [Walk.support_nil, List.mem_singleton] at hzs
    subst hzs
    exact hp _ p.start_mem_support hz
  · refine key p hb hp ⟨a, ha, Walk.nil, fun w hw => ?_⟩
    simp only [Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact ⟨hp _ p.start_mem_support, haX⟩
end Menger.Aux
