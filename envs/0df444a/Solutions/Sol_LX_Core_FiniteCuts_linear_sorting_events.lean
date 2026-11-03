-- Prove2me | solution 1 for LX.Core.FiniteCuts.linear_sorting_events
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:28:52.248476+00:00
-- url     : https://prove2.me/submissions/7c2722ed-2183-47e0-bbab-db1e16d48d52

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
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Definitions.Def_LX_ZeroGapEventTravel
import Definitions.Def_LX_ZeroGapPair
import Theorems.Thm_LX_Core_FiniteCuts_padded_sorting_events
import Theorems.Thm_LX_Core_ZeroGap_inside_linear_iff

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
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
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
/-! Compatibility for the dependent-if lemma renamed after Lean 4.33.1. -/
namespace LX
universe u

theorem dite_eq_left {α : Sort u} {p : Prop} {inst : Decidable p}
    {a : p → α} {b : ¬ p → α} (h : p) :
    (if h : p then a h else b h) = a h := dif_pos h

end LX

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
/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}













theorem embed_injective (W : Window n b) : Function.Injective (embed W) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [embed] at this
  omega





@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i

theorem permutation_outside (W : Window n b) (p : State b) (j : Fin n) (hj : ¬Contains W j) :
    permutation W p j=j := p.extendDomain_apply_not_subtype (windowEquiv W) hj

@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem displacement_mass_inverse (p : State n) :
    (∑ i : Fin n, |_root_.LX.Core.FiniteCuts.displacement p.symm i|)=∑ i : Fin n, |_root_.LX.Core.FiniteCuts.displacement p i| := by
  have h := Equiv.sum_comp p (fun i : Fin n => |_root_.LX.Core.FiniteCuts.displacement p.symm i|)
  simpa only [_root_.LX.Core.FiniteCuts.displacement,Equiv.symm_apply_apply,abs_sub_comm] using h.symm


end LX.Core.FiniteCuts

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









end LX.Core.ZeroGap

end

section
/-! Weighted paths retain the signed integer motion of tokens through the
endpoint events; their weights do not identify coordinates modulo n. -/
namespace LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem Travel.trans {events : List (Event n)} {i j k : Fin n} {a b : ℤ}
    (h : Travel events i j a) (h' : Travel events j k b) : Travel events i k (a+b) := by
  induction h with
  | refl => simpa using h'
  | head he hp ih => simpa only [add_assoc] using Travel.head he (ih h')















end LX.Core.ZeroGap

end

section
/-! Project the padded sorting trace back to its original finite interval.
On a linear event graph, graph reachability already determines integer travel. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem linear_reaches_travel (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) {i j : Fin n}
    (h : EventReaches events i j) : Travel events i j ((j : ℤ)-(i : ℤ)) := by
  induction h with
  | refl => simpa using Travel.refl (events := events) i
  | @tail a b hp he ih =>
    obtain ⟨e,he,hor⟩ := he
    have hdist : (distance e.1 e.2 : ℤ)=(e.2 : ℤ)-(e.1 : ℤ) := by
      unfold distance
      rw [Fin.sub_val_of_le (show e.1 ≤ e.2 from le_of_lt (hlinear e he))]
      have hh := hlinear e he
      omega
    have hstep : Travel events a b ((b : ℤ)-(a : ℤ)) := by
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have hm : EventMove events e.1 e.2 ((e.2 : ℤ)-(e.1 : ℤ)) :=
          ⟨e,he,Or.inl ⟨rfl,rfl,hdist.symm⟩⟩
        simpa using Travel.head hm (Travel.refl e.2)
      · have hm : EventMove events e.2 e.1 ((e.1 : ℤ)-(e.2 : ℤ)) :=
          ⟨e,he,Or.inr ⟨rfl,rfl,by omega⟩⟩
        simpa using Travel.head hm (Travel.refl e.1)
    convert ih.trans hstep using 1; ring

end LX.Core.ZeroGap

namespace LX.Core.FiniteCuts
open ZeroGap FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]





end LX.Core.FiniteCuts

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open ZeroGap FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem solution (p : State n) :
    ∃ events : List (Event n), (events.map eventSwap).prod=p ∧
      (events.length : ℤ)=(∑ i, |_root_.LX.Core.FiniteCuts.displacement p.symm i|)-(inversionNumber p : ℤ) ∧
      (∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support) ∧
      (∀ e ∈ events, e.1.val < e.2.val) ∧ events.Pairwise LaterOutside ∧
      (∀ i, Travel events i (p.symm i) (_root_.LX.Core.FiniteCuts.displacement p.symm i)) := by
  classical
  let : NeZero (2*n+1) := ⟨by omega⟩
  let W : Window (2*n+1) n := ⟨0,by omega⟩
  let q := permutation W p
  obtain ⟨events,hprod,hlen,_,ha,hl,hs⟩ := padded_sorting_events p
  let project (i : Fin (2*n+1)) : Fin n := if h : i.val < n then ⟨i.val,h⟩ else 0
  let projectEvent (e : Event (2*n+1)) : Event n := (project e.1,project e.2)
  have hins (i : Fin (2*n+1)) (hi : i ∈ q.support) : i.val < n := by
    have hc : Contains W i := by
      by_contra hh
      exact (Equiv.Perm.mem_support.mp hi) (permutation_outside W p i hh)
    simpa only [Contains,W,zero_add] using hc.2
  have hval (i : Fin (2*n+1)) (hi : i.val < n) : (project i).val=i.val := by
    simp only [project,dite_eq_left hi]
  have hemb (i : Fin (2*n+1)) (hi : i.val < n) : embed W (project i)=i := by
    apply Fin.ext
    simp only [embed,W,zero_add,hval i hi]
  have hswap (e : Event (2*n+1)) (he : e ∈ events) (i : Fin n) :
      eventSwap e (embed W i)=embed W (eventSwap (projectEvent e) i) := by
    have hh := (embed_injective W).swap_apply (project e.1) (project e.2) i
    rw [hemb _ (hins _ (ha e he).1),hemb _ (hins _ (ha e he).2)] at hh
    exact hh
  have hprod' (es : List (Event (2*n+1))) (hsub : ∀ e ∈ es, e ∈ events) (i : Fin n) :
      (es.map eventSwap).prod (embed W i)=embed W ((es.map projectEvent |>.map eventSwap).prod i) := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
      rw [ih (fun f hf => hsub f (List.mem_cons_of_mem _ hf)),hswap e (hsub e (by simp))]
  have htarget : ((events.map projectEvent).map eventSwap).prod=p := by
    apply Equiv.ext
    intro i
    apply embed_injective W
    have hh := hprod' events (fun _ h => h) i
    rw [hprod,permutation_embed] at hh
    exact hh.symm
  have hlin : ∀ e ∈ events.map projectEvent, e.1.val < e.2.val := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    simpa only [projectEvent,hval _ (hins _ (ha f hf).1),hval _ (hins _ (ha f hf).2)] using hl f hf
  have hactive : ∀ e ∈ events.map projectEvent, e.1 ∈ p.support ∧ e.2 ∈ p.support := by
    have moved (i : Fin (2*n+1)) (hi : i ∈ q.support) : project i ∈ p.support := by
      apply Equiv.Perm.mem_support.mpr
      intro hh
      apply Equiv.Perm.mem_support.mp hi
      rw [← hemb i (hins i hi)]
      change permutation W p (embed W (project i))=embed W (project i)
      rw [permutation_embed,hh]
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    exact ⟨moved _ (ha f hf).1,moved _ (ha f hf).2⟩
  have hsep : (events.map projectEvent).Pairwise LaterOutside := by
    apply List.pairwise_map.mpr
    apply hs.imp_of_mem
    intro e f he hf hef
    have he' := hlin (projectEvent e) (List.mem_map.mpr ⟨e,he,rfl⟩)
    have same (i : Fin (2*n+1)) (hi : i.val < n) :
        Inside (projectEvent e) (project i) ↔ Inside e i := by
      rw [inside_linear_iff _ he',inside_linear_iff _ (hl e he)]
      simp only [projectEvent,hval _ (hins _ (ha e he).1),hval _ (hins _ (ha e he).2),hval i hi]
    exact ⟨fun hh => hef.1 ((same f.1 (hins _ (ha f hf).1)).mp hh),
      fun hh => hef.2 ((same f.2 (hins _ (ha f hf).2)).mp hh)⟩
  refine ⟨events.map projectEvent,htarget,?_,hactive,hlin,hsep,?_⟩
  · simpa only [List.length_map,displacement_mass_inverse] using hlen
  · intro i
    exact linear_reaches_travel _ hlin (target_event_reachable _ p htarget i)
