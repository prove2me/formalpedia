-- Prove2me | solution 1 for LX.Core.ZeroGap.event_neighbor_induction_step
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:37:27.399819+00:00
-- url     : https://prove2.me/submissions/0bf1c1e3-a14a-4808-8ab2-b1235bb43311

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
import Definitions.Def_LX_ExtremeEventBranch
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ShallowNeighborSplice
import Definitions.Def_LX_TwoMovingNeighborStep
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapComponentSize
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_graph_edges_le_events
import Theorems.Thm_LX_Core_ZeroGap_head_branch_minimal
import Theorems.Thm_LX_Core_ZeroGap_head_component_union
import Theorems.Thm_LX_Core_ZeroGap_head_components_cover
import Theorems.Thm_LX_Core_ZeroGap_head_rank_adjacent
import Theorems.Thm_LX_Core_ZeroGap_opposite_moving_neighbor_step
import Theorems.Thm_LX_Core_ZeroGap_singleton_neighbor_step

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

theorem head_component_disjoint (e : Event n) (events : List (Event n))
    (hminimal : (e::events).length+1=(eventComponent (e::events) e.1).card) :
    Disjoint (eventComponent events e.1) (eventComponent events e.2) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact head_endpoints_disconnected e events hminimal
    (((mem_eventComponent events e.1 i).mp hi).trans
      (event_reaches_symm events ((mem_eventComponent events e.2 i).mp hj)))




end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]



theorem rank_adjacent_symm {S : Finset (Fin n)} {a b : Fin n}
    (h : RankAdjacent S a b) : RankAdjacent S b a := by
  refine ⟨h.2.1,h.1,Ne.symm h.2.2.1,?_⟩
  intro i hi
  simpa only [min_comm,max_comm] using h.2.2.2 i hi




end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem singleton_component_product_fixed (events : List (Event n)) (b : Fin n)
    (hb : (eventComponent events b).card=1) : (events.map eventSwap).prod b=b := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hb
  have hroot : b ∈ eventComponent events b := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  have hprod : (events.map eventSwap).prod b ∈ eventComponent events b :=
    (mem_eventComponent _ _ _).mpr (event_product_reaches events events (fun _ h => h) b)
  rw [hi,Finset.mem_singleton] at hroot hprod
  exact hprod.trans hroot.symm






end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem component_card_one_eq (events : List (Event n)) (b : Fin n)
    (hb : (eventComponent events b).card=1) : eventComponent events b={b} := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hb
  have hm : b ∈ eventComponent events b := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  rw [hi,Finset.mem_singleton] at hm
  simpa only [hm] using hi




end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem solution (e : Event n) (events : List (Event n))
    (hlinear : ∀ f ∈ e::events, f.1.val < f.2.val)
    (hsep : (e::events).Pairwise LaterOutside)
    (hmin : (e::events).length+1=(eventComponent (e::events) e.1).card)
    (hcard : 3 ≤ (eventComponent (e::events) e.1).card)
    (ih : ∀ b ∈ [e.1,e.2], 3 ≤ (eventComponent events b).card →
      IsExtreme (eventComponent events b) b → NeighborAway (componentEvents events b) b b)
    (r : Fin n) (hr : r ∈ eventComponent (e::events) e.1)
    (hext : IsExtreme (eventComponent (e::events) e.1) r) :
    NeighborAway (e::events) e.1 r := by
  classical
  have hab := head_endpoints_disconnected e events hmin
  have hba : ¬EventReaches events e.2 e.1 := fun h => hab (event_reaches_symm events h)
  have hdis := head_component_disjoint e events hmin
  have hm := head_branch_minimal e events hmin
  have ha1 : 1 ≤ (eventComponent events e.1).card := Finset.card_pos.mpr
    ⟨e.1,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  have hb1 : 1 ≤ (eventComponent events e.2).card := Finset.card_pos.mpr
    ⟨e.2,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  have hsum : 3 ≤ (eventComponent events e.1).card+(eventComponent events e.2).card := by
    rwa [head_component_union,Finset.card_union_of_disjoint hdis] at hcard
  have hl : ∀ f ∈ events, f.1.val < f.2.val := fun f hf => hlinear f (List.mem_cons_of_mem e hf)
  have hgap := head_rank_adjacent e events (hlinear e (by simp)) hsep
  rcases head_components_cover e events ((mem_eventComponent _ _ _).mp hr) with har | hbr
  · by_cases hb2 : 2 ≤ (eventComponent events e.2).card
    · apply opposite_moving_neighbor_step e events hlinear hsep hmin r
        (fun h => False.elim (hab (har.trans (event_reaches_symm events h))))
        (fun _ => hb2) ih hr hext
    · have hb : (eventComponent events e.2).card=1 := by omega
      have heqB := component_card_one_eq events e.2 hb
      have hS : eventComponent (e::events) e.1=insert e.2 (eventComponent events e.1) := by
        rw [head_component_union,heqB,Finset.union_singleton]
      have hnot : e.2 ∉ eventComponent events e.1 := fun h => hab ((mem_eventComponent _ _ _).mp h)
      obtain ⟨x,y,hxy,hp,hxr,hyr⟩ := singleton_neighbor_step events e.1 e.2 r hl hm.1 (by omega)
        hnot (singleton_component_product_fixed events e.2 hb) ((mem_eventComponent _ _ _).mpr har)
        (by rwa [← hS]) (by rwa [← hS]) (ih e.1 (by simp))
      refine ⟨x,y,?_,?_,hxr,hyr⟩
      · rwa [hS]
      · simpa only [List.map_cons,List.prod_cons,eventSwap] using hp
  · by_cases ha2 : 2 ≤ (eventComponent events e.1).card
    · apply opposite_moving_neighbor_step e events hlinear hsep hmin r (fun _ => ha2)
        (fun h => False.elim (hba (hbr.trans (event_reaches_symm events h)))) ih hr hext
    · have ha : (eventComponent events e.1).card=1 := by omega
      have heqA := component_card_one_eq events e.1 ha
      have hS : eventComponent (e::events) e.1=insert e.1 (eventComponent events e.2) := by
        rw [head_component_union,heqA,Finset.singleton_union]
      have hnot : e.1 ∉ eventComponent events e.2 := fun h => hba ((mem_eventComponent _ _ _).mp h)
      obtain ⟨x,y,hxy,hp,hxr,hyr⟩ := singleton_neighbor_step events e.2 e.1 r hl hm.2 (by omega)
        hnot (singleton_component_product_fixed events e.1 ha) ((mem_eventComponent _ _ _).mpr hbr)
        (by rw [← hS]; exact rank_adjacent_symm hgap) (by rwa [← hS]) (ih e.2 (by simp))
      refine ⟨x,y,?_,?_,hxr,hyr⟩
      · rwa [hS]
      · simpa only [List.map_cons,List.prod_cons,eventSwap,Equiv.swap_comm e.2 e.1] using hp
