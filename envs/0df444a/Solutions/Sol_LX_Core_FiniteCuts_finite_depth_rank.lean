-- Prove2me | solution 1 for LX.Core.FiniteCuts.finite_depth_rank
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:46:46.034183+00:00
-- url     : https://prove2.me/submissions/8bda367c-cb4e-4260-8629-5e40401693d0

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ZeroGapCycleRoots
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Definitions.Def_LX_ZeroGapEventTravel
import Definitions.Def_LX_ZeroGapPair
import Definitions.Def_LX_ZeroGapSorting
import Theorems.Thm_LX_Core_FiniteWindow_inversion_number_window
import Theorems.Thm_LX_Core_ZeroGap_SortingTrace_events
import Theorems.Thm_LX_Core_ZeroGap_exists_sorting_trace
import Theorems.Thm_LX_Core_ZeroGap_root_cover_count

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
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
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
/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators







theorem canonical_lift {n : ℕ} (p : State n) :
    IsLift p 0 (fun i => (p.symm i : ℤ) - (i : ℤ)) := by
  constructor
  · rw [Finset.sum_sub_distrib]
    have h := Equiv.sum_comp p.symm (fun i : Fin n => (i : ℤ))
    rw [h]
    simp
  · intro i
    simp [Int.ModEq]




















end LX.Core.AffineLift

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
/-! Displacements of finite permutations define balanced affine lifts.
The canonical finite lift has phase zero. -/
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {b : ℕ}



theorem canonical_lift (p : State b) : AffineLift.IsLift p.symm 0 (_root_.LX.Core.FiniteCuts.displacement p) := by
  unfold _root_.LX.Core.FiniteCuts.displacement
  simpa only [Equiv.symm_symm] using AffineLift.canonical_lift p.symm


end LX.Core.FiniteCuts

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

theorem contains_embed (W : Window n b) (i : Fin b) : Contains W (embed W i) :=
  (windowEquiv W i).property

theorem contains_iff (W : Window n b) (j : Fin n) : Contains W j ↔ ∃ i, embed W i=j := by
  constructor
  · intro h
    refine ⟨(windowEquiv W).symm ⟨j,h⟩, ?_⟩
    exact congrArg Subtype.val ((windowEquiv W).apply_symm_apply ⟨j,h⟩)
  · rintro ⟨i,rfl⟩
    exact contains_embed W i

@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i

theorem permutation_outside (W : Window n b) (p : State b) (j : Fin n) (hj : ¬Contains W j) :
    permutation W p j=j := p.extendDomain_apply_not_subtype (windowEquiv W) hj

@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl


theorem displacement_embed (W : Window n b) (p : State b) (i : Fin b) :
    _root_.LX.Core.FiniteCuts.displacement (permutation W p) (embed W i)=_root_.LX.Core.FiniteCuts.displacement p i := by
  unfold _root_.LX.Core.FiniteCuts.displacement
  rw [permutation_embed]
  simp [embed]

theorem displacement_outside (W : Window n b) (p : State b) (j : Fin n) (hj : ¬Contains W j) :
    _root_.LX.Core.FiniteCuts.displacement (permutation W p) j=0 := by
  simp [_root_.LX.Core.FiniteCuts.displacement,permutation_outside W p j hj]


end LX.Core.FiniteWindow

end

section
/-! The inversion terms reversed by a zero-gap endpoint swap each drop from
one to zero. Other endpoint terms are exchanged in pairs. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem negative_quotient_term {z : ℤ} (hz : z < 0) (hn : -z ≤ (n : ℤ)) : (z/(n : ℤ)).natAbs=1 := by
  rw [Int.ediv_eq_neg_one_of_neg_of_le hz hn]
  decide

theorem nonnegative_quotient_term {z : ℤ} (hz : 0 ≤ z) (hn : z < (n : ℤ)) : (z/(n : ℤ)).natAbs=0 := by
  rw [Int.ediv_eq_zero_of_lt hz hn]
  decide







end LX.Core.ZeroGap

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



theorem canonical_inversion_term [NeZero n] (p : State n) (i j : Fin n) :
    (if i < j then (((p j : ℤ)-(p i : ℤ))/(n : ℤ)).natAbs else 0)=
      if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0 := by
  have hi0 : (0 : ℤ) ≤ p i := by positivity
  have hj0 : (0 : ℤ) ≤ p j := by positivity
  have hin : (p i : ℤ) < n := by exact_mod_cast (p i).isLt
  have hjn : (p j : ℤ) < n := by exact_mod_cast (p j).isLt
  by_cases hij : i.val < j.val
  · have hij' : i < j := hij
    rw [if_pos hij']
    by_cases hp : (p j).val < (p i).val
    · have hp' : (p j : ℤ) < p i := by exact_mod_cast hp
      rw [ZeroGap.negative_quotient_term (by omega) (by omega)]
      simp [hij,hp]
    · have hp' : (p i : ℤ) ≤ p j := by exact_mod_cast (show (p i).val ≤ (p j).val by omega)
      rw [ZeroGap.nonnegative_quotient_term (by omega) (by omega)]
      simp [hij,hp]
  · have hij' : ¬i < j := hij
    simp [hij',hij]

theorem canonical_inversion_count [NeZero n] (p : State n) :
    LiftedModel.inversionCount (fun i : Fin n => (p i : ℤ))=inversionNumber p := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact canonical_inversion_term p i j
end LX.Core.FiniteCuts

namespace LX.Core.FiniteWindow
open scoped BigOperators
variable {n b : ℕ}










end LX.Core.FiniteWindow

end

section
/-! Exact mass and cut-load identities for an embedded finite window. -/
namespace LX.Core.FiniteWindow
open scoped BigOperators
variable {n b : ℕ}

theorem sum_window (W : Window n b) (f : Fin n → ℤ)
    (hzero : ∀ j, ¬Contains W j → f j=0) :
    (∑ j : Fin n, f j)=∑ i : Fin b, f (embed W i) := by
  classical
  let S := Finset.univ.image (embed W)
  have hsub : (∑ j ∈ S, f j)=∑ j : Fin n, f j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    apply hzero j
    intro h
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp h
    exact hnot (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [← hsub]
  exact Finset.sum_image (fun i _ j _ h => embed_injective W h)

theorem displacement_mass (W : Window n b) (p : State b) :
    (∑ j : Fin n, |_root_.LX.Core.FiniteCuts.displacement (permutation W p) j|)=
      ∑ i : Fin b, |_root_.LX.Core.FiniteCuts.displacement p i| := by
  rw [sum_window W _ (fun j hj => by rw [displacement_outside W p j hj,abs_zero])]
  simp only [displacement_embed]



end LX.Core.FiniteWindow

end

section
namespace LX.Core.FiniteWindow
variable {n b : ℕ}

theorem permutation_support (W : Window n b) (p : State b) :
    (permutation W p).support=p.support.image (embed W) := by
  classical
  ext j
  constructor
  · intro hj
    have hcontains : Contains W j := by
      by_contra hout
      exact (Equiv.Perm.mem_support.mp hj) (permutation_outside W p j hout)
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp hcontains
    apply Finset.mem_image.mpr
    refine ⟨i,?_,rfl⟩
    apply Equiv.Perm.mem_support.mpr
    intro hi
    apply (Equiv.Perm.mem_support.mp hj)
    rw [permutation_embed,hi]
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    apply Equiv.Perm.mem_support.mpr
    rw [permutation_embed]
    intro h
    exact (Equiv.Perm.mem_support.mp hi) (embed_injective W h)

theorem permutation_support_card (W : Window n b) (p : State b) :
    (permutation W p).support.card=p.support.card := by
  rw [permutation_support,Finset.card_image_of_injective _ (embed_injective W)]



end LX.Core.FiniteWindow

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

theorem cycle_root_count {p : State n} {events : List (Event n)}
    (hprod : (events.map eventSwap).prod=p) :
    p.support.card ≤ events.length+(p⁻¹).cycleFactorsFinset.card := by
  classical
  have h := root_cover_count events (cycleRoots p) (cycle_roots_cover hprod)
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  simp only [cycleRoots,List.length_append,List.length_map,Finset.length_toList,
    Finset.card_compl,Finset.card_univ,Fintype.card_fin,Equiv.Perm.support_inv] at h
  omega


end LX.Core.ZeroGap

end

section
/-! The sorting trace yields an ordered event list in the original physical
coordinates, together with factorization and noncrossing certificates. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem sorting_events {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∃ events : List (Event n), (events.map eventSwap).prod=p ∧
      (events.length : ℤ)=(∑ i : Fin n, |d i|)-
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ∧
      (∀ e ∈ events, e.1 ≠ e.2) ∧ (∀ e ∈ events, d e.1 ≠ 0 ∧ d e.2 ≠ 0) ∧
      events.Pairwise LaterOutside ∧ (∀ e ∈ events, 2*distance e.1 e.2 < n) ∧
      (∀ i, Travel events i (p.symm i) (d i)) := by
  obtain ⟨M,ht,hcount⟩ := exists_sorting_trace hd hshort
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hshortEvents,htravel⟩ := ht.events hd hshort
  exact ⟨events,hprod,by rw [hlen]; omega,hneq,hactive,hsep,hshortEvents,htravel⟩



end LX.Core.ZeroGap

end

section
/-! Reflection-rank and packet-cycle bounds come from the actual sorting
events. Combined with majorization they pay the two-arc numerical budget. -/
namespace LX.Core.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem reflection_rank_inversion_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    (p.support.card : ℤ)+(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      (∑ i : Fin n, |d i|)+((p⁻¹).cycleFactorsFinset.card : ℤ) := by
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hsmall,htravel⟩ := sorting_events hd hshort
  have h := cycle_root_count hprod
  omega



end LX.Core.ZeroGap

namespace LX.Core.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]


end LX.Core.FiniteGaps

end

section
namespace LX.Core.FiniteWindow
variable {n b : ℕ}

/-- Extending a permutation by fixed positions preserves its nontrivial cycle count. -/
theorem permutation_cycle_count (W : Window n b) (p : State b) :
    (permutation W p).cycleFactorsFinset.card = p.cycleFactorsFinset.card := by
  classical
  have h := congrArg Multiset.card (Equiv.Perm.cycleType_extendDomain (g := p) (windowEquiv W))
  simpa [Equiv.Perm.cycleType, permutation] using h

end LX.Core.FiniteWindow

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}




end LX.Core.FiniteCuts

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- A finite depth inequality for every permutation, without a shortness
hypothesis. Padding is used only inside the proof of the event bound. -/
theorem solution (p : State n) :
    (inversionNumber p : ℤ)+(p.support.card : ℤ) ≤
      (∑ i : Fin n, |_root_.LX.Core.FiniteCuts.displacement p i|)+(p.cycleFactorsFinset.card : ℤ) := by
  classical
  letI : NeZero (2*n+1) := ⟨by omega⟩
  let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
  let q : State (2*n+1) := FiniteWindow.permutation W p
  have hshort (j : Fin (2*n+1)) : 2*|_root_.LX.Core.FiniteCuts.displacement q j| < (2*n+1 : ℕ) := by
    by_cases hj : FiniteWindow.Contains W j
    · obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hj
      simp only [q,FiniteWindow.displacement_embed]
      have hi0 : (0 : ℤ) ≤ i := by positivity
      have hp0 : (0 : ℤ) ≤ p i := by positivity
      have hin : (i : ℤ) < n := by exact_mod_cast i.isLt
      have hpn : (p i : ℤ) < n := by exact_mod_cast (p i).isLt
      have hh : |_root_.LX.Core.FiniteCuts.displacement p i| < (n : ℤ) := by
        unfold _root_.LX.Core.FiniteCuts.displacement
        rw [abs_lt]
        constructor <;> omega
      push_cast
      omega
    · simp only [q,FiniteWindow.displacement_outside W p j hj,abs_zero,mul_zero]
      positivity
  have hr := ZeroGap.reflection_rank_inversion_bound (canonical_lift q) hshort
  have hend : (fun i : Fin (2*n+1) => (i : ℤ)+_root_.LX.Core.FiniteCuts.displacement q i)=(fun i => (q i : ℤ)) := by
    funext i
    unfold _root_.LX.Core.FiniteCuts.displacement
    omega
  change ((q⁻¹).support.card : ℤ)+(LiftedModel.inversionCount (fun i => (i : ℤ)+_root_.LX.Core.FiniteCuts.displacement q i) : ℤ) ≤
    (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)+(q.cycleFactorsFinset.card : ℤ) at hr
  rw [Equiv.Perm.support_inv,hend,canonical_inversion_count] at hr
  have hI := FiniteWindow.inversion_number_window W p
  have hs := FiniteWindow.permutation_support_card W p
  have hm := FiniteWindow.displacement_mass W p
  change inversionNumber q=inversionNumber p at hI
  change q.support.card=p.support.card at hs
  change (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)=(∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|) at hm
  have hc := FiniteWindow.permutation_cycle_count W p
  change q.cycleFactorsFinset.card=p.cycleFactorsFinset.card at hc
  rw [hI,hs,hm,hc] at hr
  simpa only [add_comm] using hr
