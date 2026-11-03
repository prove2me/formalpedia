-- Prove2me | solution 1 for LX.Core.ZeroGap.minimal_interval_event_unit_arrow
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:43:04.347888+00:00
-- url     : https://prove2.me/submissions/179dcfbf-37ef-410d-8c8f-5dcbbc4d2e80

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ShallowNeighborSplice
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapCycleRoots
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_exists_interval_event_component
import Theorems.Thm_LX_Core_ZeroGap_minimal_tree_rank_neighbor
import Theorems.Thm_LX_Core_ZeroGap_root_cover_equality_component_minimal
import Theorems.Thm_LX_Core_ZeroGap_selected_product_agrees

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
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
/-! Cycle representatives and fixed points give a root cover of the sorting
event graph; all cycles inside the packet can share one root. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]



theorem cycle_root_mem {q : State n} (hq : q.IsCycle) : cycleRoot q ∈ q.support := by
  classical
  have hne := hq.nonempty_support
  simp only [cycleRoot,dif_pos hne]
  exact Finset.min'_mem _ _

theorem cycle_root_same_cycle {g q : State n} (hq : q ∈ g.cycleFactorsFinset)
    {i : Fin n} (hi : i ∈ q.support) : g.SameCycle (cycleRoot q) i := by
  classical
  have hroot : cycleRoot q ∈ q.support := cycle_root_mem (q := q) (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1
  have he : q=g.cycleOf i := Equiv.Perm.cycle_is_cycleOf (f := g) (c := q) hi hq
  have hroot' : cycleRoot q ∈ (g.cycleOf i).support := by rw [← he]; exact hroot
  exact ((Equiv.Perm.mem_support_cycleOf_iff (f := g) (x := i) (y := cycleRoot q)).mp hroot').1.symm



theorem cycle_roots_cover {p : State n} {events : List (Event n)}
    (hprod : (events.map eventSwap).prod=p) :
    ∀ i : Fin n, ∃ r ∈ cycleRoots p, EventReaches events r i := by
  classical
  intro i
  by_cases hi : i ∈ (p⁻¹).support
  · obtain ⟨q,hq,hiq⟩ := (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).mp hi
    refine ⟨cycleRoot q,?_,cycle_event_reachable events p hprod (cycle_root_same_cycle hq hiq)⟩
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨q,by simpa using hq,rfl⟩
  · exact ⟨i,List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_compl.mpr hi)),Relation.ReflTransGen.refl⟩




end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]





/-- A minimal transposition factorization is a forest on its actual event
carriers. The cycle representatives supply the cover, including fixed points. -/
theorem minimal_factorization_component_minimal (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p)
    (hminimal : events.length+(p⁻¹).cycleFactorsFinset.card=p.support.card) (root : Fin n) :
    (componentEvents events root).length+1=(eventComponent events root).card := by
  classical
  apply root_cover_equality_component_minimal events (cycleRoots p) (cycle_roots_cover hprod) _ root
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  simp only [cycleRoots,List.length_append,List.length_map,Finset.length_toList,
    Finset.card_compl,Finset.card_univ,Fintype.card_fin,Equiv.Perm.support_inv]
  omega




end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ}





theorem rank_adjacent_of_interval {T S : Finset (Fin n)} (hT : CarrierInterval T S)
    {x y : Fin n} (hxy : RankAdjacent T x y) : RankAdjacent S x y := by
  refine ⟨hT.1 hxy.1,hT.1 hxy.2.1,hxy.2.2.1,?_⟩
  intro z hz hz'
  exact hxy.2.2.2 z (hT.2 x hxy.1 y hxy.2.1 z hz hz'.1 hz'.2) hz'













end LX.Core.ZeroGap

end

section
namespace LX.Core.FiniteCuts
variable {n : ℕ}

theorem full_carrier_neighbor_unit {x y : Fin n}
    (h : ZeroGap.RankAdjacent Finset.univ x y) : |(y : ℤ)-(x : ℤ)|=1 := by
  by_contra hunit
  have hne : x.val ≠ y.val := fun he => h.2.2.1 (Fin.ext he)
  have hgap : min x.val y.val+1 < max x.val y.val := by
    simp only [abs_eq_max_neg] at hunit
    omega
  let z : Fin n := ⟨min x.val y.val+1,by have := x.isLt; have := y.isLt; omega⟩
  apply h.2.2.2 z (Finset.mem_univ z)
  change min x.val y.val < min x.val y.val+1 ∧ min x.val y.val+1 < max x.val y.val
  exact ⟨by omega,hgap⟩


end LX.Core.FiniteCuts

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- A minimal separated factorization on a nonempty interval support has
an actual unit arrow. The carrier is extracted, not assumed to be a cycle. -/
theorem solution (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p)
    (hactive : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hne : p.support.Nonempty) (hinterval : CarrierInterval p.support Finset.univ)
    (hminimal : events.length+(p⁻¹).cycleFactorsFinset.card=p.support.card) :
    ∃ i : Fin n, |_root_.LX.Core.FiniteCuts.displacement p i|=1 := by
  classical
  obtain ⟨root,_,hc,hint⟩ := exists_interval_event_component events p hprod hactive hlinear hsep hne hinterval
  have hmin := minimal_factorization_component_minimal events p hprod hminimal root
  have hsub : (componentEvents events root).Sublist events := List.filter_sublist
  obtain ⟨x,y,hxy,harrow⟩ := minimal_tree_rank_neighbor (componentEvents events root) root
    (fun e he => hlinear e (hsub.subset he)) (hsep.sublist hsub)
    (by rwa [selected_component_eq]) (by rwa [selected_component_eq])
  rw [selected_component_eq] at hxy
  have hagree := selected_product_agrees events root x ((mem_eventComponent _ _ _).mp hxy.1)
  rw [hprod] at hagree
  have hp : p x=y := hagree.symm.trans harrow
  refine ⟨x,?_⟩
  unfold _root_.LX.Core.FiniteCuts.displacement
  rw [hp]
  exact FiniteCuts.full_carrier_neighbor_unit (rank_adjacent_of_interval hint hxy)
