-- Prove2me | solution 1 for LX.AnchoredPhases.odd_zero_reserve_adjacent_fixed
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:41:25.426564+00:00
-- url     : https://prove2.me/submissions/6c5fb3cb-bcbb-426a-bb83-5a68da42f321

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
import Definitions.Def_LX_AnchorReserveRigidity
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_StrictBandInversionCapacity
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_AnchoredPhases_cyclic_pair_reverse_coordinate
import Theorems.Thm_LX_AnchoredPhases_three_fixed_matching_unique_cyclic_gap_two
import Theorems.Thm_LX_Core_AffineLift_majorized_level_count
import Theorems.Thm_LX_Core_AffineLift_short_coordinates
import Theorems.Thm_LX_Core_FiniteCuts_inherited_capacity_equality_noncrossing
import Theorems.Thm_LX_Core_FiniteCuts_involutive_of_cycles_are_swaps
import Theorems.Thm_LX_Core_FiniteCuts_shifted_capacity_equality_support
import Theorems.Thm_LX_MatchingGeometry_exists_adjacent_fixed

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.MatchingGeometry
end LX.MatchingGeometry
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

theorem cast_eq_of_modEq {a b : ℤ} (h : Int.ModEq (n : ℤ) a b) :
    (a : Fin n) = (b : Fin n) := by
  apply Fin.ext
  rw [Fin.val_intCast, Fin.val_intCast]
  exact congrArg Int.toNat h




















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
/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]
































theorem cast_eq_iff_modEq (a b : ℤ) :
    (a : Fin n) = (b : Fin n) ↔ Int.ModEq (n : ℤ) a b := by
  constructor
  · intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_intCast] at hh
    have hi := congrArg (fun k : ℕ => (k : ℤ)) hh
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hn0),
      Int.toNat_of_nonneg (Int.emod_nonneg b hn0)] at hi
    exact hi
  · exact AffineLift.cast_eq_of_modEq




end LX.Core.LiftedModel

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



theorem clockwise_representative_bounds (p : State n) (i : Fin n) :
    (i : ℤ) ≤ clockwiseRepresentative p i ∧ clockwiseRepresentative p i < (i : ℤ)+n := by
  have hi := i.isLt
  have hp := (p i).isLt
  unfold clockwiseRepresentative
  split_ifs <;> omega

theorem clockwise_representative_modEq (p : State n) (i : Fin n) :
    Int.ModEq (n : ℤ) (clockwiseRepresentative p i) (p i : ℤ) := by
  unfold clockwiseRepresentative
  split_ifs <;> simp [Int.ModEq]



theorem clockwise_representative_mass (p : State n) :
    (∑ i : Fin n, (clockwiseRepresentative p i-(i : ℤ))) =
      (n : ℤ)*((descendingPositions p).card : ℤ) := by
  have hp : (∑ i : Fin n, _root_.LX.Core.FiniteCuts.displacement p i)=0 := (canonical_lift p).1
  have hpoint (i : Fin n) : clockwiseRepresentative p i-(i : ℤ) =
      _root_.LX.Core.FiniteCuts.displacement p i+(if (p i).val < i.val then (n : ℤ) else 0) := by
    unfold clockwiseRepresentative _root_.LX.Core.FiniteCuts.displacement
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, hp, zero_add]
  rw [← Finset.sum_filter]
  simp [descendingPositions, mul_comm]




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
namespace LX.Core



@[simp] theorem Letter.eval_inverse {n : ℕ} [NeZero n] (c : Letter) :
    c.inverse.eval (n := n) = (c.eval)⁻¹ := by
  cases c <;> simp [inverse, Letter.eval, L, R, X]








end LX.Core

end

section
/-! Directed LX words. No inverse generator is included in the alphabet.
The target bound is a proposition, not an axiom or an assumed estimate. -/
namespace LX









@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by
  simp [eval]





























end LX

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]











theorem displacement_balance (p : State n) (a : Fin n) : ∑ i, _root_.LX.AnchoredPhases.displacement p a i = 0 := by
  unfold _root_.LX.AnchoredPhases.displacement
  rw [Finset.sum_sub_distrib, clockwise_representative_mass]
  simp [height]

theorem displacement_band (p : State n) (a i : Fin n) :
    0 ≤ _root_.LX.AnchoredPhases.displacement p a i + height p a ∧ _root_.LX.AnchoredPhases.displacement p a i + height p a < (n : ℤ) := by
  have h := clockwise_representative_bounds (permutation p a) i
  unfold _root_.LX.AnchoredPhases.displacement
  omega





/-- The candidate is a balanced lift of the original permutation, not an abstract strip. -/
theorem is_lift (p : State n) (a : Fin n) :
    LX.Core.AffineLift.IsLift p.symm (phase p a) (_root_.LX.AnchoredPhases.displacement p a) := by
  refine ⟨displacement_balance p a, ?_⟩
  intro i
  have hq : Int.ModEq (n : ℤ) (permutation p a i : ℤ)
      ((p i : ℤ)+(a : ℤ)-(p a : ℤ)) := by
    apply (LX.Core.LiftedModel.cast_eq_iff_modEq _ _).mp
    simp [permutation, Int.cast_sub, Int.cast_add, add_sub_assoc]
  have hm := ((clockwise_representative_modEq (permutation p a) i).trans hq).sub_right (height p a : ℤ)
  change Int.ModEq (n : ℤ) ((i : ℤ)+_root_.LX.AnchoredPhases.displacement p a i) ((p i : ℤ)+phase p a)
  convert hm using 1 <;> simp only [_root_.LX.AnchoredPhases.displacement, phase] <;> ring












end LX.AnchoredPhases

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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]





theorem shifted_anchor_permutation (p : State n) (a : Fin n) :
    LX.Core.FiniteCuts.shiftedLiftPermutation p.symm (phase p a) (height p a)=permutation p a := by
  apply Equiv.ext
  intro i
  change p i+((phase p a+(height p a : ℤ) : ℤ) : Fin n)=p i+(a-p a)
  simp only [phase,Int.cast_add,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self]
  ring














end LX.AnchoredPhases

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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]





theorem three_fixed_matching_no_cyclic_adjacent (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (hm : Majorized (_root_.LX.AnchoredPhases.displacement p a)) (hn : n=2*height p a+3)
    (hinv : Function.Involutive (permutation p a)) :
    ∀ i : Fin n,permutation p a i ≠ i+1 := by
  intro i hi
  have hr := cyclic_pair_reverse_coordinate p a i 1 (by omega) (by omega) (hinv i) hi
  have hu := (short_coordinates (is_lift p a).1 hm (permutation p a i)).1
  rw [hr] at hu
  omega






end LX.AnchoredPhases

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

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Extract the adjacent fixed pair directly from the zero-reserve source;
no unpaid-word assumption or auxiliary numerical constant is used. -/
theorem solution (p : State n) (a : Fin n)
    (hn7 : 7 ≤ n) (hn : n=2*height p a+3)
    (hm : Majorized (_root_.LX.AnchoredPhases.displacement p a)) (hz : anchorReserve p a=0) :
    ∃ u : Fin n,permutation p a u=u ∧ permutation p a (u+1)=u+1 := by
  have hd := is_lift p a
  have heq : (LX.Core.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+_root_.LX.AnchoredPhases.displacement p a i) : ℤ)=
      (height p a : ℤ)*((n : ℤ)-height p a-1) := by
    change (inversions (_root_.LX.AnchoredPhases.displacement p a) : ℤ)=_
    unfold anchorReserve at hz
    omega
  obtain ⟨hs,hc,hdef,hpairs⟩ := inherited_capacity_equality_pairs hd.1 hm hd
    (height p a : ℤ) (by omega) (displacement_band p a) (fun _ hi => hi) heq
  simp only [shifted_anchor_permutation] at hs hc hdef hpairs
  have hinv := involutive_of_cycles_are_swaps (permutation p a) hpairs
  have hnc : NoncrossingPairs (permutation p a) := by
    intro i j k l hij hjk hkl hik
    have ht := inherited_capacity_equality_noncrossing hd.1 hm hd
      (height p a : ℤ) (by omega) (displacement_band p a) (fun _ hi => hi) heq
    simpa only [shifted_anchor_permutation] using ht i j k l hij hjk hkl (by
      simpa only [shifted_anchor_permutation] using hik)
  have hsupport : 4 ≤ (permutation p a).support.card := by omega
  exact LX.MatchingGeometry.exists_adjacent_fixed (permutation p a) hinv hnc hsupport
    (three_fixed_matching_no_cyclic_adjacent (by omega) p a hm hn hinv)
    (three_fixed_matching_unique_cyclic_gap_two (by omega) p a hm hn hinv)
