-- Prove2me | solution 1 for LX.Core.ZeroGap.exists_interval_event_component
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:32:12.942437+00:00
-- url     : https://prove2.me/submissions/b04fb439-cba2-4589-a58a-48a54d73afbd

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
import Definitions.Def_LX_ShallowNeighborSplice
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_component_inside_hull

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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- In a linear separated trace with interval support, a moving component
of minimum physical width has no holes. -/
theorem solution (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p)
    (hactive : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hne : p.support.Nonempty) (hinterval : CarrierInterval p.support Finset.univ) :
    ∃ root : Fin n, root ∈ p.support ∧ 2 ≤ (eventComponent events root).card ∧
      CarrierInterval (eventComponent events root) Finset.univ := by
  classical
  let C := eventComponent events
  have hroot (r : Fin n) : r ∈ C r := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  let lo (r : Fin n) := (C r).min' ⟨r,hroot r⟩
  let hi (r : Fin n) := (C r).max' ⟨r,hroot r⟩
  have hlo (r : Fin n) : lo r ∈ C r := Finset.min'_mem _ _
  have hhi (r : Fin n) : hi r ∈ C r := Finset.max'_mem _ _
  have hbounds (r i : Fin n) (h : i ∈ C r) : (lo r).val ≤ i.val ∧ i.val ≤ (hi r).val :=
    ⟨Finset.min'_le _ _ h,Finset.le_max' _ _ h⟩
  have hsub (r : Fin n) (hr : r ∈ p.support) : C r ⊆ p.support := by
    intro i hi
    have hp := (mem_eventComponent _ _ _).mp hi
    induction hp with
    | refl => exact hr
    | @tail a b hp he ih =>
      obtain ⟨e,he,hor⟩ := he
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (hactive e he).2
      · exact (hactive e he).1
  obtain ⟨r,hr,hmin⟩ := p.support.exists_min_image (fun r => (hi r).val-(lo r).val) hne
  have hclosed (z : Fin n) (hzlo : (lo r).val < z.val) (hzhi : z.val < (hi r).val) : z ∈ C r := by
    by_contra hz
    have hzmove : z ∈ p.support := hinterval.2 (lo r) (hsub r hr (hlo r))
      (hi r) (hsub r hr (hhi r)) z (Finset.mem_univ _) (by omega) (by omega)
    have hrl := (mem_eventComponent _ _ _).mp (hlo r)
    have hrh := (mem_eventComponent _ _ _).mp (hhi r)
    have hlh := (event_reaches_symm events hrl).trans hrh
    have hav : ¬ EventReaches events (lo r) z := by
      intro hh
      exact hz ((mem_eventComponent _ _ _).mpr (hrl.trans hh))
    have hb (i : Fin n) (hh : EventReaches events (lo r) i) :
        (lo r).val ≤ i.val ∧ i.val ≤ (hi r).val :=
      hbounds r i ((mem_eventComponent _ _ _).mpr (hrl.trans hh))
    have inner (j : Fin n) (hj : j ∈ C z) : (lo r).val < j.val ∧ j.val < (hi r).val :=
      component_inside_hull events hlinear hsep (lo r) z (hi r) hzlo hzhi hlh hav
        (lo r).val (hi r).val hb j ((mem_eventComponent _ _ _).mp hj)
    have hlz := inner (lo z) (hlo z)
    have hhz := inner (hi z) (hhi z)
    have hzz := hbounds z (lo z) (hlo z)
    have hrr := hbounds r (lo r) (hlo r)
    have hminimal := hmin z hzmove
    omega
  refine ⟨r,hr,?_,Finset.subset_univ _,?_⟩
  · have hpr : p r ∈ C r := by
      apply (mem_eventComponent _ _ _).mpr
      have hh := event_product_reaches events events (fun _ h => h) r
      rwa [hprod] at hh
    exact Finset.one_lt_card.mpr ⟨r,hroot r,p r,hpr,(Equiv.Perm.mem_support.mp hr).symm⟩
  · intro x hx y hy z _ hz1 hz2
    have hx' := hbounds r x hx
    have hy' := hbounds r y hy
    exact hclosed z (by omega) (by omega)
