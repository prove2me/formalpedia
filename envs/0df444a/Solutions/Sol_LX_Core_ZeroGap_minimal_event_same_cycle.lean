-- Prove2me | solution 1 for LX.Core.ZeroGap.minimal_event_same_cycle
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:33:19.033192+00:00
-- url     : https://prove2.me/submissions/c44c8c4e-47a5-49ed-909c-5580fed39c70

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapComponentSize
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_component_selected_size
import Theorems.Thm_LX_Core_ZeroGap_graph_edges_le_events
import Theorems.Thm_LX_Core_ZeroGap_head_branch_minimal
import Theorems.Thm_LX_Core_ZeroGap_head_components_cover
import Theorems.Thm_LX_Core_ZeroGap_same_cycle_after_orbit_merge
import Theorems.Thm_LX_Core_ZeroGap_selected_same_cycle
import Theorems.Thm_LX_Core_ZeroGap_swap_distinct_orbits_same_cycle

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

section
/-!
The L/R/X Cayley graph on `Equiv.Perm (Fin n)`. Right multiplication acts
on positions: `L` rotates the list to the left, `R` to the right, and `X`
exchanges its first two entries. The extended diameter avoids the convention
that a disconnected graph has natural-valued diameter zero.
-/
namespace LX.Core



















@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_cons {n : ℕ} [NeZero n] (a : Letter) (w : List Letter) :
    eval (n := n) (a :: w) = a.eval * eval w := by simp [eval]

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by simp [eval]






end LX.Core

end

section
/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]






















@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]









end LX.Core.AffineLift

end

section
/-! Physical positions, a paid cursor, and literal L/R/X words.
Every physical operation is proved to induce the same visible generator.
A realized balanced lift ends at the original target in its exact orientation. -/
namespace LX.Core.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift



variable {n : ℕ} [NeZero n]















@[simp] theorem visible_initial : visible (initial (n := n)) = 1 := by
  simp [visible, initial]


end LX.Core.PhysicalModel

end

section
/-! Connected components of the event graph contain the cycles of the
original permutation and are invariant under it. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem event_reaches_symm (events : List (Event n)) {i j : Fin n} (h : EventReaches events i j) :
    EventReaches events j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact (Relation.ReflTransGen.single (event_edge_symm events he)).trans ih

theorem event_swap_reaches (events : List (Event n)) (e : Event n) (he : e ∈ events) (i : Fin n) :
    EventReaches events i (eventSwap e i) := by
  by_cases hi : i=e.1
  · subst i
    simp only [eventSwap,Equiv.swap_apply_left]
    exact Relation.ReflTransGen.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  · by_cases hi' : i=e.2
    · subst i
      simp only [eventSwap,Equiv.swap_apply_right]
      exact Relation.ReflTransGen.single ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
    · simp only [eventSwap,Equiv.swap_apply_of_ne_of_ne hi hi']
      exact Relation.ReflTransGen.refl

theorem event_product_reaches (events part : List (Event n)) (hsub : ∀ e ∈ part, e ∈ events) (i : Fin n) :
    EventReaches events i ((part.map eventSwap).prod i) := by
  induction part with
  | nil => exact Relation.ReflTransGen.refl
  | cons e rest ih =>
    have hp := ih (fun f hf => hsub f (List.mem_cons_of_mem _ hf))
    have he := event_swap_reaches events e (hsub e (by simp)) ((rest.map eventSwap).prod i)
    exact hp.trans he

theorem target_event_reachable (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) (i : Fin n) : EventReaches events i (p.symm i) := by
  have h := event_product_reaches events events (fun _ h => h) (p.symm i)
  rw [hprod,p.apply_symm_apply] at h
  exact event_reaches_symm events h

theorem cycle_event_reachable (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) {i j : Fin n} (hc : (p⁻¹).SameCycle i j) :
    EventReaches events i j := by
  obtain ⟨k,rfl⟩ := hc.exists_nat_pow_eq
  clear hc
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    have he := target_event_reachable events p hprod (((p⁻¹)^k) i)
    simpa only [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.inv_def] using ih.trans he







end LX.Core.ZeroGap

end

section
/-! Every connected component of the event graph uses at least one fewer
exchange events than its number of vertices. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]





theorem component_root_path (events : List (Event n)) (root : Fin n) {j : Fin n}
    (hp : EventReaches events root j) :
    (componentGraph events root).Reachable (rootVertex events root)
      ⟨j,(mem_eventComponent events root j).mpr hp⟩ := by
  induction hp with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u v hp he ih =>
    by_cases huv : u=v
    · subst v
      exact ih
    · have ha : (componentGraph events root).Adj
          ⟨u,(mem_eventComponent events root u).mpr hp⟩
          ⟨v,(mem_eventComponent events root v).mpr (hp.tail he)⟩ :=
        ⟨fun h => huv (congrArg Subtype.val h),he⟩
      exact ih.trans ha.reachable

theorem component_graph_connected (events : List (Event n)) (root : Fin n) :
    (componentGraph events root).Connected := by
  letI : Nonempty {i : Fin n // i ∈ eventComponent events root} := ⟨rootVertex events root⟩
  constructor
  intro i j
  have hi := component_root_path events root ((mem_eventComponent events root i.val).mp i.property)
  have hj := component_root_path events root ((mem_eventComponent events root j.val).mp j.property)
  exact hi.symm.trans hj

theorem event_component_size (events : List (Event n)) (root : Fin n) :
    (eventComponent events root).card ≤ events.length+1 := by
  classical
  let G := componentGraph events root
  have hvertices := (component_graph_connected events root).card_vert_le_card_edgeSet_add_one
  have hedges := graph_edges_le_events G events Subtype.val Subtype.val_injective (fun i j h => h.2)
  have hcard : Nat.card {i : Fin n // i ∈ eventComponent events root}=(eventComponent events root).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  change Nat.card {i : Fin n // i ∈ eventComponent events root} ≤ Nat.card G.edgeSet+1 at hvertices
  rw [hcard] at hvertices
  omega



end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]



/-- Minimal event count forces the first event to join different tail
components. This avoids assuming the graph is a tree as a new premise. -/
theorem head_endpoints_disconnected (e : Event n) (events : List (Event n))
    (hminimal : (e::events).length+1=(eventComponent (e::events) e.1).card) :
    ¬EventReaches events e.1 e.2 := by
  intro hab
  have hsub : eventComponent (e::events) e.1 ⊆ eventComponent events e.1 := by
    intro i hi
    apply (mem_eventComponent events e.1 i).mpr
    have h := head_components_cover e events ((mem_eventComponent (e::events) e.1 i).mp hi)
    exact h.elim id (fun h => hab.trans h)
  have hcard := Finset.card_le_card hsub
  have htail := event_component_size events e.1
  simp only [List.length_cons] at hminimal
  omega






end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]







theorem component_edge_selected {events : List (Event n)} {root i j : Fin n}
    (hi : EventReaches events root i) (he : EventEdge events i j) :
    EventEdge (componentEvents events root) i j := by
  classical
  obtain ⟨e,he,h⟩ := he
  have hr : EventReaches events root e.1 := by
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hi
    · exact hi.tail ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
  exact ⟨e,by simp [componentEvents,he,hr],h⟩





@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem event_reaches_mono {xs ys : List (Event n)} (hsub : ∀ e ∈ xs, e ∈ ys)
    {a b : Fin n} (hp : EventReaches xs a b) : EventReaches ys a b := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih =>
    obtain ⟨e,he,h⟩ := he
    exact ih.tail ⟨e,hsub e he,h⟩










end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem selected_reaches_iff (events : List (Event n)) (root i : Fin n) :
    EventReaches (componentEvents events root) root i ↔ EventReaches events root i := by
  classical
  constructor
  · apply event_reaches_mono
    intro e he
    exact (List.mem_filter.mp he).1
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp he ih => exact ih.tail (component_edge_selected hp he)

theorem selected_component_eq (events : List (Event n)) (root : Fin n) :
    eventComponent (componentEvents events root) root=eventComponent events root := by
  ext i
  simp only [mem_eventComponent,selected_reaches_iff]





end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem event_component_reroot (events : List (Event n)) {a b : Fin n}
    (hab : EventReaches events a b) : eventComponent events a=eventComponent events b := by
  ext i
  simp only [mem_eventComponent]
  exact ⟨fun h => (event_reaches_symm events hab).trans h,fun h => hab.trans h⟩

theorem minimal_events_reachable (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) :
    ∀ e ∈ events, EventReaches events root e.1 := by
  classical
  have hc := component_selected_size events root
  have hl : (componentEvents events root).length ≤ events.length := List.length_filter_le _ _
  have heq : (componentEvents events root).length=events.length := by omega
  have h := List.length_filter_eq_length_iff.mp heq
  intro e he
  exact of_decide_eq_true (h e he)









end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- A minimal connected list of transpositions has one orbit on its entire carrier. -/
theorem solution (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) :
    ∀ i ∈ eventComponent events root, (events.map eventSwap).prod.SameCycle root i := by
  classical
  have main : ∀ m : ℕ, ∀ (xs : List (Event n)) (r : Fin n), xs.length=m →
      xs.length+1=(eventComponent xs r).card →
      ∀ i ∈ eventComponent xs r, (xs.map eventSwap).prod.SameCycle r i := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro xs r hlen hm
      cases xs with
      | nil =>
        intro i hi
        have hr : r ∈ eventComponent [] r := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
        have hc : (eventComponent [] r).card ≤ 1 := by simpa using hm.symm.le
        have he : r=i := Finset.card_le_one.mp hc r hr i hi
        subst i
        exact Equiv.Perm.SameCycle.refl _ _
      | cons e rest =>
        have hrhead := minimal_events_reachable (e::rest) r hm e (by simp)
        have hcarrier := event_component_reroot (e::rest) hrhead
        have hm' : (e::rest).length+1=(eventComponent (e::rest) e.1).card := by rwa [← hcarrier]
        have branches := head_branch_minimal e rest hm'
        have hnot := head_endpoints_disconnected e rest hm'
        let q := (rest.map eventSwap).prod
        have hnq : ¬q.SameCycle e.1 e.2 := by
          intro hs
          exact hnot (cycle_event_reachable rest q rfl hs.inv)
        have hbranch (b : Fin n)
            (hb : (componentEvents rest b).length+1=(eventComponent rest b).card)
            (i : Fin n) (hi : i ∈ eventComponent rest b) : q.SameCycle b i := by
          have hle := List.length_filter_le (fun e => decide (EventReaches rest b e.1)) rest
          have hlt : (componentEvents rest b).length < m := by
            change (componentEvents rest b).length ≤ rest.length at hle
            simp only [List.length_cons] at hlen
            omega
          have hh := ih (componentEvents rest b).length hlt (componentEvents rest b) b rfl
            (by rwa [selected_component_eq]) i (by rwa [selected_component_eq])
          exact selected_same_cycle rest b i hh
        have hall (i : Fin n) (hi : i ∈ eventComponent (e::rest) e.1) :
            (eventSwap e*q).SameCycle e.1 i := by
          have hp := head_components_cover e rest ((mem_eventComponent _ _ _).mp hi)
          rcases hp with hp | hp
          · exact same_cycle_after_orbit_merge q e.1 e.2 hnq
              (hbranch e.1 branches.1 i ((mem_eventComponent _ _ _).mpr hp))
          · exact (swap_distinct_orbits_same_cycle q e.1 e.2 hnq).trans
              (same_cycle_after_orbit_merge q e.1 e.2 hnq
                (hbranch e.2 branches.2 i ((mem_eventComponent _ _ _).mpr hp)))
        intro i hi
        have hr : r ∈ eventComponent (e::rest) e.1 :=
          (mem_eventComponent _ _ _).mpr (event_reaches_symm _ hrhead)
        rw [hcarrier] at hi
        exact (hall r hr).symm.trans (hall i hi)
  exact main events.length events root rfl hmin
