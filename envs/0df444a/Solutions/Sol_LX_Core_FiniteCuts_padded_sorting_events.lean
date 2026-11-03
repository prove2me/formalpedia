-- Prove2me | solution 1 for LX.Core.FiniteCuts.padded_sorting_events
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:46:47.060476+00:00
-- url     : https://prove2.me/submissions/29f90d9c-412f-4c60-a183-bbeba3231ad5

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
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventTravel
import Definitions.Def_LX_ZeroGapPair
import Definitions.Def_LX_ZeroGapSorting
import Theorems.Thm_LX_Core_FiniteCuts_inversion_number_inverse
import Theorems.Thm_LX_Core_FiniteWindow_inversion_number_window
import Theorems.Thm_LX_Core_ZeroGap_SortingTrace_events
import Theorems.Thm_LX_Core_ZeroGap_exists_sorting_trace

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

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- An actual separated linear sorting trace for every finite permutation,
obtained by padding with fixed positions. -/
theorem solution (p : State n) :
    let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
    let q := FiniteWindow.permutation W p
    ∃ events : List (ZeroGap.Event (2*n+1)),
      (events.map ZeroGap.eventSwap).prod=q ∧
      (events.length : ℤ)=(∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ) ∧
      (∀ e ∈ events, e.1 ≠ e.2) ∧
      (∀ e ∈ events, e.1 ∈ q.support ∧ e.2 ∈ q.support) ∧
      (∀ e ∈ events, e.1.val < e.2.val) ∧ events.Pairwise ZeroGap.LaterOutside := by
  classical
  letI : NeZero (2*n+1) := ⟨by omega⟩
  let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
  let q := FiniteWindow.permutation W p
  have hshort (j : Fin (2*n+1)) : 2*|_root_.LX.Core.FiniteCuts.displacement q.symm j| < (2*n+1 : ℕ) := by
    by_cases hj : FiniteWindow.Contains W j
    · obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hj
      simp only [q,FiniteWindow.permutation_symm,FiniteWindow.displacement_embed]
      have hi0 : (0 : ℤ) ≤ i := by positivity
      have hp0 : (0 : ℤ) ≤ p.symm i := by positivity
      have hin : (i : ℤ) < n := by exact_mod_cast i.isLt
      have hpn : (p.symm i : ℤ) < n := by exact_mod_cast (p.symm i).isLt
      have hh : |_root_.LX.Core.FiniteCuts.displacement p.symm i| < (n : ℤ) := by
        unfold _root_.LX.Core.FiniteCuts.displacement
        rw [abs_lt]
        constructor <;> omega
      push_cast
      omega
    · simp only [q,FiniteWindow.permutation_symm,
        FiniteWindow.displacement_outside W p.symm j hj,abs_zero,mul_zero]
      positivity
  have hd : AffineLift.IsLift q 0 (_root_.LX.Core.FiniteCuts.displacement q.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift q.symm
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hsmall,_⟩ := ZeroGap.sorting_events hd hshort
  have hF : (fun j : Fin (2*n+1) => (j : ℤ)+_root_.LX.Core.FiniteCuts.displacement q.symm j)=
      (fun j => (q.symm j : ℤ)) := by funext j; unfold _root_.LX.Core.FiniteCuts.displacement; omega
  rw [hF,canonical_inversion_count] at hlen
  have hInv : inversionNumber q.symm=inversionNumber q := inversion_number_inverse q
  rw [hInv,displacement_mass_inverse] at hlen
  have hmass : (∑ j, |_root_.LX.Core.FiniteCuts.displacement q j|)=∑ i, |_root_.LX.Core.FiniteCuts.displacement p i| := FiniteWindow.displacement_mass W p
  have hI : inversionNumber q=inversionNumber p := FiniteWindow.inversion_number_window W p
  have hcontains (j : Fin (2*n+1)) (hj : j ∈ q.support) : FiniteWindow.Contains W j := by
    by_contra hh
    exact (Equiv.Perm.mem_support.mp hj) (FiniteWindow.permutation_outside W p j hh)
  have ha : ∀ e ∈ events, e.1 ∈ q.support ∧ e.2 ∈ q.support := by
    have hm (j : Fin (2*n+1)) (hj : _root_.LX.Core.FiniteCuts.displacement q.symm j ≠ 0) : j ∈ q.support := by
      have hne : q.symm j ≠ j := by
        intro hh
        exact hj (by simp only [_root_.LX.Core.FiniteCuts.displacement,hh,sub_self])
      have hh : j ∈ (q⁻¹).support := Equiv.Perm.mem_support.mpr hne
      simpa only [Equiv.Perm.support_inv] using hh
    intro e he
    exact ⟨hm e.1 (hactive e he).1,hm e.2 (hactive e he).2⟩
  have hlinear : ∀ e ∈ events, e.1.val < e.2.val := by
    intro e he
    have h0 := hcontains e.1 (ha e he).1
    have h1 := hcontains e.2 (ha e he).2
    change 0 ≤ e.1.val ∧ e.1.val < 0+n at h0
    change 0 ≤ e.2.val ∧ e.2.val < 0+n at h1
    have hne := hneq e he
    have hsmall' := hsmall e he
    by_contra hh
    have hne' : e.1.val ≠ e.2.val := fun h => hne (Fin.ext h)
    have hrev : e.2 < e.1 := by change e.2.val < e.1.val; omega
    unfold ZeroGap.distance at hsmall'
    rw [Fin.coe_sub_iff_lt.mpr hrev] at hsmall'
    omega
  rw [hmass,hI] at hlen
  exact ⟨events,hprod,hlen,hneq,ha,hlinear,hsep⟩
