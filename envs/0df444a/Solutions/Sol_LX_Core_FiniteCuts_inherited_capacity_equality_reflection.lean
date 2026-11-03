-- Prove2me | solution 1 for LX.Core.FiniteCuts.inherited_capacity_equality_reflection
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:11:16.055553+00:00
-- url     : https://prove2.me/submissions/a6669847-bfa6-486b-81b0-1d25bf120bec

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
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_StrictBandInversionCapacity
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_Core_AffineLift_majorized_level_count
import Theorems.Thm_LX_Core_FiniteCuts_inherited_capacity_equality_reflection_at_zero
import Theorems.Thm_LX_Core_FiniteCuts_shifted_capacity_equality_support
import Theorems.Thm_LX_Core_FiniteCuts_shifted_fixed_iff_negative_extreme
import Theorems.Thm_LX_Core_RotationWords_inversion_count_recentered
import Theorems.Thm_LX_Core_RotationWords_recentered_lift

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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.WordReflection
end LX.Core.WordReflection
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
/-! Majorization bounds the energy of any balanced subset by its number of
positions. No separate majorization assumption on the pruned lift is needed. -/
namespace LX.Core.AffineLift
open scoped BigOperators
variable {n : ℕ}

theorem majorized_neg {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : Majorized d) :
    Majorized (fun i => -d i) := by
  intro S
  have hs := Finset.sum_add_sum_compl S d
  rw [hd] at hs
  have hc : S.card ≤ n := by simpa using Finset.card_le_univ S
  have h := hm Sᶜ
  simp only [Finset.card_compl,Finset.card_univ,Fintype.card_fin,Nat.cast_sub hc] at h
  rw [Finset.sum_neg_distrib]
  nlinarith


end LX.Core.AffineLift
namespace LX.Core.PrunedLift
open scoped BigOperators Fin.NatCast
variable {n : ℕ} [NeZero n]


end LX.Core.PrunedLift

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem cycle_support_card_sum (p : State n) :
    ∑ q ∈ p.cycleFactorsFinset, q.support.card=p.support.card := by
  classical
  obtain ⟨l,hn,heq⟩ := p.cycleFactorsFinset.exists_list_nodup_eq
  have h := (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset hn).mp heq.symm
  have hc := Equiv.Perm.card_support_prod_list_of_pairwise_disjoint h.2.1
  rw [h.2.2] at hc
  rw [← heq, List.sum_toFinset _ hn]
  exact hc.symm




end LX.Core.FiniteCuts

end

section
/-! A zero-displacement phase lift is an actual rotation. Its final rotation
is explicitly paid by an LX.Core word of length at most n-1. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_power_apply (k : ℕ) (i : Fin n) : (L n ^ k) i = i + (k : Fin n) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [L, finRotate_apply, Nat.cast_add, add_comm, add_left_comm]


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
/-! Recenter a phase lift at an arbitrary port. The local target is chosen so
that paid entry and exit rotations recover the original visible permutation. -/
namespace LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem local_displacement_zero (d : Fin n → ℤ) (r : Fin n) :
    localDisplacement d r 0=d r := by
  simp [localDisplacement, AffineLift.rotation_power_apply]






end LX.Core.RotationWords

end

section
/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}



















@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem mem_descendingPositions (p : State n) (i : Fin n) :
    i ∈ descendingPositions p ↔ (p i).val < i.val := by
  simp [descendingPositions]









@[simp] theorem descending_positions_one : descendingPositions (1 : State n) = ∅ := by
  ext i
  simp




















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Equality in the minimum cycle-size bound forces every cycle to be a swap. -/
theorem cycles_are_swaps_of_support_eq_twice_count (p : State n)
    (heq : p.support.card=2*p.cycleFactorsFinset.card) :
    ∀ q ∈ p.cycleFactorsFinset, q.IsSwap := by
  classical
  have hlo : ∀ q ∈ p.cycleFactorsFinset, 2 ≤ q.support.card :=
    fun q hq => (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1.two_le_card_support
  have hs : (∑ _q ∈ p.cycleFactorsFinset, 2)=∑ q ∈ p.cycleFactorsFinset, q.support.card := by
    rw [cycle_support_card_sum, heq]
    simp [Nat.mul_comm]
  have hall := (Finset.sum_eq_sum_iff_of_le hlo).mp hs
  intro q hq
  exact Equiv.Perm.card_support_eq_two.mp (hall q hq).symm


end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



@[simp] theorem mem_fixedPositions (p : State n) (i : Fin n) :
    i ∈ fixedPositions p ↔ p i=i := by simp [fixedPositions]

theorem fixed_positions_card (p : State n) :
    ((fixedPositions p).card : ℤ)=(n : ℤ)-(p.support.card : ℤ) := by
  have hs : fixedPositions p=Finset.univ \ p.support := by
    ext i
    simp [Equiv.Perm.mem_support]
  have hc : p.support.card ≤ n := by simpa using p.support.card_le_univ
  rw [hs,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hc]







end LX.Core.FiniteCuts

end

section
namespace LX.Core.AffineLift
open scoped BigOperators
variable {n : ℕ}



theorem majorized_negative_level_count {d : Fin n → ℤ}
    (hd : ∑ i, d i=0) (hm : Majorized d) (h : ℤ) (hh : 2*h ≤ (n : ℤ)) :
    ((Finset.univ.filter (fun i => d i= -h)).card : ℤ) ≤ (n : ℤ)-2*h := by
  have hb := majorized_level_count (majorized_neg hd hm) h hh
  simpa only [neg_eq_iff_eq_neg] using hb

/-- Filling may change other coordinates; preserving negative extremes suffices here. -/
theorem inherited_negative_level_count {d e : Fin n → ℤ}
    (hd : ∑ i, d i=0) (hm : Majorized d) (h : ℤ) (hh : 2*h ≤ (n : ℤ))
    (hinherit : ∀ i, e i= -h → d i= -h) :
    ((Finset.univ.filter (fun i => e i= -h)).card : ℤ) ≤ (n : ℤ)-2*h := by
  have hs : Finset.univ.filter (fun i => e i= -h) ⊆
      Finset.univ.filter (fun i => d i= -h) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinherit i (Finset.mem_filter.mp hi).2⟩
  have hc : ((Finset.univ.filter (fun i => e i= -h)).card : ℤ) ≤
      ((Finset.univ.filter (fun i => d i= -h)).card : ℤ) := by exact_mod_cast Finset.card_le_card hs
  exact hc.trans (majorized_negative_level_count hd hm h hh)


end LX.Core.AffineLift

end

section
/-! Coordinate changes preserve majorization and the entire strongly
connected root packet. -/
namespace LX.Core.AffineLift
open scoped BigOperators
variable {n : ℕ}

theorem majorized_comp {d : Fin n → ℤ} (hm : Majorized d) (e : State n) :
    Majorized (fun i => d (e i)) := by
  intro S
  have h := hm (S.image e)
  rw [Finset.card_image_of_injective _ e.injective,
    Finset.sum_image (fun i _ j _ hij => e.injective hij)] at h
  exact h
end LX.Core.AffineLift

namespace LX.Core.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem majorized_recenter {d : Fin n → ℤ} (hm : AffineLift.Majorized d) (r : Fin n) :
    AffineLift.Majorized (localDisplacement d r) :=
  AffineLift.majorized_comp hm (rotation r)


end LX.Core.RotationWords

namespace LX.Core.WordReflection
open scoped BigOperators
variable {n : ℕ} [NeZero n]

end LX.Core.WordReflection

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Equality for a completion with inherited negative extremes forces a shallow
matching. The original majorization is used only to derive the extreme count. -/
theorem inherited_capacity_equality_pairs {p : State n} {c : ℤ}
    {original d : Fin n → ℤ} (horiginal : ∑ i, original i=0)
    (hmaj : AffineLift.Majorized original) (hd : AffineLift.IsLift p c d)
    (h : ℤ) (hh : 2*h ≤ (n : ℤ))
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (hinherit : ∀ i, d i= -h → original i= -h)
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1)) :
    let q := shiftedLiftPermutation p c h
    (q.support.card : ℤ)=2*h ∧ (q.cycleFactorsFinset.card : ℤ)=h ∧
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)-(inversionNumber q : ℤ)=h ∧
      (∀ r ∈ q.cycleFactorsFinset, r.IsSwap) := by
  have hext := AffineLift.inherited_negative_level_count horiginal hmaj h hh hinherit
  obtain ⟨hs,hc,hdef⟩ := shifted_capacity_equality_support hd h hband heq hext
  dsimp only
  refine ⟨hs,hc,hdef,?_⟩
  apply cycles_are_swaps_of_support_eq_twice_count
  have he : ((shiftedLiftPermutation p c h).support.card : ℤ)=
      2*((shiftedLiftPermutation p c h).cycleFactorsFinset.card : ℤ) := by omega
  exact_mod_cast he


end LX.Core.FiniteCuts

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The fixed-point cut is selected from the equality case itself. -/
theorem solution
    {p : State n} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p 0 d) (h : ℤ)
    (hparity : (n : ℤ)=2*h+1 ∨ (n : ℤ)=2*h+2)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) (hupper : ∀ i, d i ≤ h)
    (hinheritNeg : ∀ i, d i= -h → original i= -h)
    (hinheritPos : ∀ i, d i=h → original i=h)
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1)) :
    ∃ r : Fin n, ∀ i : Fin n, (localTarget p 0 r).symm i= -i-(h : Fin n) := by
  classical
  have hh : 2*h ≤ (n : ℤ) := by omega
  obtain ⟨hs,_,_,_⟩ := inherited_capacity_equality_pairs horiginal hmaj hd h hh hband hinheritNeg heq
  let q := shiftedLiftPermutation p 0 h
  have hf := fixed_positions_card q
  change (q.support.card : ℤ)=2*h at hs
  have hpos : 0 < (fixedPositions q).card := by omega
  obtain ⟨r,hr⟩ := Finset.card_pos.mp hpos
  have hrfix : q r=r := (mem_fixedPositions q r).mp hr
  have hdr : d r= -h := (shifted_fixed_iff_negative_extreme hd h hband r).mp hrfix
  have hdlocal : AffineLift.IsLift (localTarget p 0 r) 0 (localDisplacement d r) :=
    recentered_lift (0 : Fin n) r (by simpa using hd)
  have hbalance : (∑ i, localDisplacement original r i)=0 := by
    unfold localDisplacement
    rw [Equiv.sum_comp (L n^r.val)]
    exact horiginal
  have hmajor := majorized_recenter hmaj r
  have hbandlocal : ∀ i, 0 ≤ localDisplacement d r i+h ∧
      localDisplacement d r i+h < (n : ℤ) := fun i => hband ((L n^r.val) i)
  have heqlocal : (LiftedModel.inversionCount
      (fun i : Fin n => (i : ℤ)+localDisplacement d r i) : ℤ)=h*((n : ℤ)-h-1) := by
    rw [inversion_count_recentered (0 : Fin n) r (by simpa using hd)]
    exact heq
  have hzero : shiftedLiftPermutation (localTarget p 0 r) 0 h 0=0 := by
    apply (shifted_fixed_iff_negative_extreme hdlocal h hbandlocal 0).mpr
    rw [local_displacement_zero]
    exact hdr
  have href := inherited_capacity_equality_reflection_at_zero hbalance hmajor hdlocal h hparity
    hbandlocal (fun i => hupper ((L n^r.val) i))
    (fun i hi => hinheritNeg ((L n^r.val) i) hi)
    (fun i hi => hinheritPos ((L n^r.val) i) hi) heqlocal hzero
  refine ⟨r,?_⟩
  intro i
  have hi := href i
  change (localTarget p 0 r).symm i+((0+h : ℤ) : Fin n)= -i at hi
  simp only [zero_add] at hi
  exact eq_sub_of_add_eq hi
