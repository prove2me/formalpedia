-- Prove2me | solution 1 for LX.Core.ZeroGap.singleton_neighbor_step
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:31:22.367667+00:00
-- url     : https://prove2.me/submissions/95a91351-d334-4029-80b5-a2da274070ab

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
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_component_selected_size
import Theorems.Thm_LX_Core_ZeroGap_event_product_fixed
import Theorems.Thm_LX_Core_ZeroGap_rank_adjacent_after_extreme_insertion
import Theorems.Thm_LX_Core_ZeroGap_selected_product_agrees

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

theorem minimal_product_support_subset (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) :
    (events.map eventSwap).prod.support ⊆ eventComponent events root := by
  classical
  intro i hi
  by_contra hnot
  have hne : i ∉ endpoints events := by
    intro hm
    obtain ⟨e,he,hor⟩ := (mem_endpoints events i).mp hm
    have hroot := minimal_events_reachable events root hmin e he
    apply hnot
    apply (mem_eventComponent events root i).mpr
    rcases hor with rfl | rfl
    · exact hroot
    · exact hroot.tail ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  exact (Equiv.Perm.mem_support.mp hi) (event_product_fixed events i hne)

theorem minimal_two_vertex_support (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hcard : (eventComponent events root).card=2) :
    (events.map eventSwap).prod.support=eventComponent events root := by
  classical
  have hlen : events.length=1 := by omega
  have hp : (events.map eventSwap).prod.support.card=2 := by
    obtain ⟨e,rfl⟩ := List.length_eq_one_iff.mp hlen
    have he := hlinear e (by simp)
    have hne : e.1 ≠ e.2 := by intro h; have := congrArg Fin.val h; omega
    simpa [eventSwap] using Equiv.Perm.card_support_swap hne
  exact Finset.eq_of_subset_of_card_le (minimal_product_support_subset events root hmin) (by omega)





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





theorem remaining_pair_adjacent (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hext : IsExtreme ({a,b,c} : Finset (Fin n)) a) :
    RankAdjacent ({a,b,c} : Finset (Fin n)) c b := by
  classical
  refine ⟨by simp,by simp,Ne.symm hbc,?_⟩
  intro z hz hz'
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · rcases hext with h | h
    · have := h b (by simp); have := h c (by simp); omega
    · have := h b (by simp); have := h c (by simp); omega
  · omega
  · omega


end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Adding a singleton next to an extreme preserves an inductive neighbor;
the three-vertex case is constructed directly. -/
theorem solution (events : List (Event n)) (a b r : Fin n)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hmin : (componentEvents events a).length+1=(eventComponent events a).card)
    (hcard : 2 ≤ (eventComponent events a).card)
    (hb : b ∉ eventComponent events a)
    (hfixed : (events.map eventSwap).prod b=b)
    (hr : r ∈ eventComponent events a)
    (hgap : RankAdjacent (insert b (eventComponent events a)) a b)
    (hext : IsExtreme (insert b (eventComponent events a)) r)
    (ih : 3 ≤ (eventComponent events a).card → IsExtreme (eventComponent events a) a →
      NeighborAway (componentEvents events a) a a) :
    ∃ x y, RankAdjacent (insert b (eventComponent events a)) x y ∧
      (Equiv.swap a b*(events.map eventSwap).prod) x=y ∧ x ≠ r ∧ y ≠ r := by
  classical
  by_cases hra : r=a
  · subst r
    have hextA : IsExtreme (eventComponent events a) a := by
      rcases hext with h | h
      · exact Or.inl (fun i hi => h i (Finset.mem_insert_of_mem hi))
      · exact Or.inr (fun i hi => h i (Finset.mem_insert_of_mem hi))
    by_cases hc3 : 3 ≤ (eventComponent events a).card
    · obtain ⟨x,y,hxy,hp,hxa,hya⟩ := ih hc3 hextA
      rw [selected_component_eq] at hxy
      have hxp := (mem_eventComponent events a x).mp hxy.1
      have hq : (events.map eventSwap).prod x=y := (selected_product_agrees events a x hxp).symm.trans hp
      have hyb : y ≠ b := fun h => hb (h ▸ hxy.2.1)
      refine ⟨x,y,rank_adjacent_after_extreme_insertion _ a b hext hgap hxy hxa hya,?_,hxa,hya⟩
      rw [Equiv.Perm.mul_apply,hq,Equiv.swap_apply_of_ne_of_ne hya hyb]
    · have hc2 : (eventComponent events a).card=2 := by omega
      let q : State n := ((componentEvents events a).map eventSwap).prod
      have hlin : ∀ e ∈ componentEvents events a, e.1.val < e.2.val :=
        fun e he => hlinear e (List.mem_filter.mp he).1
      have hs : q.support=eventComponent events a := by
        have h := minimal_two_vertex_support (componentEvents events a) a
          (by rwa [selected_component_eq]) hlin (by rwa [selected_component_eq])
        simpa only [selected_component_eq] using h
      have ha : a ∈ q.support := by rwa [hs]
      have hne : q a ≠ a := Equiv.Perm.mem_support.mp ha
      have hqa : q a ∈ q.support := by
        apply Equiv.Perm.mem_support.mpr
        intro h
        exact hne (q.injective h)
      have hreturn : q (q a)=a := by
        have hswap : q.IsSwap := Equiv.Perm.card_support_eq_two.mp (by rwa [hs])
        obtain ⟨u,v,_,heq⟩ := hswap
        rw [heq]
        simp
      have hpair : ({a,q a} : Finset (Fin n))=eventComponent events a := by
        apply Finset.eq_of_subset_of_card_le
        · intro i hi
          simp only [Finset.mem_insert,Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hr
          · rwa [← hs]
        · simp [hc2,Ne.symm hne]
      have hab : a ≠ b := fun h => hb (h ▸ hr)
      have hbc : b ≠ q a := by intro h; apply hb; rw [h]; rwa [← hs]
      have hS : insert b (eventComponent events a)=({a,b,q a} : Finset (Fin n)) := by
        rw [← hpair,Finset.insert_comm b a]
      have hex : IsExtreme ({a,b,q a} : Finset (Fin n)) a := by rwa [hS] at hext
      have hneighbor := remaining_pair_adjacent a b (q a) hab (Ne.symm hne) hbc hex
      have htail : (events.map eventSwap).prod (q a)=a := by
        have hm : q a ∈ eventComponent events a := by rwa [← hs]
        exact (selected_product_agrees events a (q a) ((mem_eventComponent _ _ _).mp hm)).symm.trans hreturn
      refine ⟨q a,b,?_,?_,hne,Ne.symm hab⟩
      · rwa [hS]
      · rw [Equiv.Perm.mul_apply,htail,Equiv.swap_apply_left]
  · have hbr : b ≠ r := fun h => hb (h.symm ▸ hr)
    refine ⟨b,a,rank_adjacent_symm hgap,?_,hbr,Ne.symm hra⟩
    rw [Equiv.Perm.mul_apply,hfixed,Equiv.swap_apply_right]
