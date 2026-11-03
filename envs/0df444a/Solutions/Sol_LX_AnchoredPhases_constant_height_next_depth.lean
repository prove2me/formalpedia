-- Prove2me | solution 1 for LX.AnchoredPhases.constant_height_next_depth
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:04:50.745456+00:00
-- url     : https://prove2.me/submissions/eea65e4f-770b-4539-8409-e2df1b9ddb87

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_DepthCrowding
import Definitions.Def_LX_FiniteCrossPairCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_StrictBandInversionCapacity
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapInversionTerms
import Theorems.Thm_LX_AffineScan_displacement_depth_width_bound
import Theorems.Thm_LX_AffineScan_exists_depth_extreme
import Theorems.Thm_LX_AnchoredPhases_constant_height_below_count
import Theorems.Thm_LX_AnchoredPhases_depth_eq_height_iff_fixed
import Theorems.Thm_LX_Core_FiniteCuts_cycle_descending_count_lt_support
import Theorems.Thm_LX_Core_FiniteCuts_displacement_mass_eq_twice_leftDepth
import Theorems.Thm_LX_Core_FiniteCuts_finite_depth_rank
import Theorems.Thm_LX_Core_FiniteCuts_inversion_row_balance
import Theorems.Thm_LX_Core_FiniteCuts_shifted_balanced_descending_count
import Theorems.Thm_LX_Core_FiniteCuts_sum_upper_sym

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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.PairCore
end LX.PairCore
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

theorem lift_residue {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    i + (d i : Fin n) = p.symm i + (c : Fin n) := by
  have h := cast_eq_of_modEq (hd.2 i)
  simpa using h


















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
/-! Integer division is determined by lower and upper quotient bounds.
This arithmetic identity is used in the finite-coordinate estimates. -/
namespace LX.Core.PeriodicBuffer

theorem quotient_eq_of_bounds {M x q : ℤ} (hM : 0 < M)
    (hlo : q*M ≤ x) (hhi : x < (q+1)*M) : x/M = q := by
  have ha := (Int.le_ediv_iff_mul_le hM).mpr hlo
  have hb := (Int.ediv_lt_iff_lt_mul hM).mpr hhi
  omega


end LX.Core.PeriodicBuffer

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



theorem descending_positions_mul (p q : State n) (h : p.Disjoint q) :
    descendingPositions (p*q) = descendingPositions p ∪ descendingPositions q := by
  ext i
  simp only [Finset.mem_union, mem_descendingPositions]
  rcases h i with hi | hi
  · have hm : (p*q) i = q i := by rw [h.commute.eq]; simp [hi]
    rw [hm,hi]
    omega
  · have hm : (p*q) i = p i := by simp [hi]
    rw [hm,hi]
    omega

theorem descending_positions_disjoint (p q : State n) (h : p.Disjoint q) :
    Disjoint (descendingPositions p) (descendingPositions q) := by
  apply Finset.disjoint_left.mpr
  intro i hp hq
  have hp := (mem_descendingPositions p i).mp hp
  have hq := (mem_descendingPositions q i).mp hq
  rcases h i with hi | hi
  · rw [hi] at hp; omega
  · rw [hi] at hq; omega

theorem descending_count_mul (p q : State n) (h : p.Disjoint q) :
    (descendingPositions (p*q)).card =
      (descendingPositions p).card + (descendingPositions q).card := by
  rw [descending_positions_mul p q h,
    Finset.card_union_of_disjoint (descending_positions_disjoint p q h)]

@[simp] theorem descending_positions_one : descendingPositions (1 : State n) = ∅ := by
  ext i
  simp

theorem descending_count_list_prod (l : List (State n)) (h : l.Pairwise Equiv.Perm.Disjoint) :
    (descendingPositions l.prod).card = (l.map (fun p => (descendingPositions p).card)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp h
    have hd : p.Disjoint l.prod := Equiv.Perm.disjoint_prod_right l hp
    simpa using (descending_count_mul p l.prod hd).trans (by rw [ih hl])

theorem descending_count_cycle_sum (p : State n) :
    (descendingPositions p).card = ∑ q ∈ p.cycleFactorsFinset, (descendingPositions q).card := by
  classical
  obtain ⟨l,hn,heq⟩ := p.cycleFactorsFinset.exists_list_nodup_eq
  have h := (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset hn).mp heq.symm
  rw [← heq, List.sum_toFinset _ hn, ← descending_count_list_prod l h.2.1, h.2.2]



/-- Each cycle contributes at least one position that does not move left. -/
theorem descending_count_add_cycles_le_support (p : State n) :
    (descendingPositions p).card + p.cycleFactorsFinset.card ≤ p.support.card := by
  classical
  have h : ∑ q ∈ p.cycleFactorsFinset, ((descendingPositions q).card+1) ≤
      ∑ q ∈ p.cycleFactorsFinset, q.support.card := by
    apply Finset.sum_le_sum
    intro q hq
    exact cycle_descending_count_lt_support (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    ← descending_count_cycle_sum, cycle_support_card_sum] using h

/-- The finite depth bound with the left-moving position count needed by the strict-band cap. -/
theorem finite_depth_descending (p : State n) :
    (inversionNumber p : ℤ) + ((descendingPositions p).card : ℤ) ≤
      ∑ i : Fin n, |_root_.LX.Core.FiniteCuts.displacement p i| := by
  have hr := finite_depth_rank p
  have hc : ((descendingPositions p).card : ℤ) + (p.cycleFactorsFinset.card : ℤ) ≤
      (p.support.card : ℤ) := by exact_mod_cast descending_count_add_cycles_le_support p
  omega





/-- This is the finite input `2 dep - I ≥ #D` to the affine capacity identity. -/
theorem leftDepth_inversion_deficit (p : State n) :
    ((descendingPositions p).card : ℤ) ≤ 2*leftDepth p-(inversionNumber p : ℤ) := by
  have h := finite_depth_descending p
  rw [displacement_mass_eq_twice_leftDepth] at h
  omega




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

theorem clockwise_representative_unique (p : State n) (g : Fin n → ℤ)
    (hb : ∀ i : Fin n, (i : ℤ) ≤ g i ∧ g i < (i : ℤ)+n)
    (hm : ∀ i : Fin n, Int.ModEq (n : ℤ) (g i) (p i : ℤ)) :
    g = clockwiseRepresentative p := by
  funext i
  have h := ((hm i).trans (clockwise_representative_modEq p i).symm).sub_right (i : ℤ)
  have hg := hb i
  have hc := clockwise_representative_bounds p i
  unfold Int.ModEq at h
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega

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

theorem sum_inversion_indicator (p : State n) :
    (∑ i, ∑ j, inversionIndicator p i j)=(inversionNumber p : ℤ) := by
  simp only [inversionNumber, inversionIndicator, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]





theorem sum_descending_indicator (p : State n) :
    (∑ i, descendingIndicator p i)=((descendingPositions p).card : ℤ) := by
  unfold descendingIndicator
  rw [← Finset.sum_filter]
  simp [descendingPositions]

theorem weighted_displacement_eq_leftDepth (p : State n) :
    (∑ i, descendingIndicator p i*((i : ℤ)-(p i : ℤ)))=leftDepth p := by
  simp only [leftDepth, descendingPositions, Finset.sum_filter, descendingIndicator,
    ite_mul, one_mul, zero_mul]

/-- Internal inversions cancel when row balances are summed over left-moving positions. -/
theorem weighted_inversion_balance (p : State n) :
    (∑ i, ∑ j, inversionIndicator p i j*(descendingIndicator p j-descendingIndicator p i))=
      leftDepth p := by
  simp_rw [mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => inversionIndicator p i j*descendingIndicator p j)]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, inversion_row_balance, mul_comm]
  exact weighted_displacement_eq_leftDepth p



end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}





/-- There are |D|(n-|D|) unordered pairs with exactly one endpoint in D. -/
theorem sum_cross_pair_indicator (p : State n) :
    (∑ i, ∑ j, crossPairIndicator p i j)=
      ((descendingPositions p).card : ℤ)*((n : ℤ)-(descendingPositions p).card) := by
  unfold crossPairIndicator
  rw [sum_upper_sym (fun i j => descendingIndicator p i*(1-descendingIndicator p j))
    (fun i => by unfold descendingIndicator; split_ifs <;> norm_num)]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_descending_indicator, Finset.sum_sub_distrib,
    sum_descending_indicator]
  simp


end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem clockwise_pair_quotient (p : State n) (i j : Fin n) :
    (clockwiseRepresentative p j-clockwiseRepresentative p i)/(n : ℤ)=
      (if (p j).val < (p i).val then (-1 : ℤ) else 0)+
        descendingIndicator p j-descendingIndicator p i := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hi := (p i).isLt
  have hj := (p j).isLt
  unfold clockwiseRepresentative descendingIndicator
  split_ifs <;> apply PeriodicBuffer.quotient_eq_of_bounds hn <;> omega

/-- The affine pair contribution is a finite inversion, plus a cross-pair
charge, minus twice the weighted finite inversion correction. -/
theorem clockwise_inversion_term (p : State n) (i j : Fin n) :
    (ZeroGap.inversionTerm (clockwiseRepresentative p) i j : ℤ)=
      inversionIndicator p i j+crossPairIndicator p i j-
        2*(inversionIndicator p i j*(descendingIndicator p j-descendingIndicator p i)) := by
  by_cases hij : i < j
  · rw [ZeroGap.inversionTerm, if_pos hij, clockwise_pair_quotient]
    unfold inversionIndicator crossPairIndicator descendingIndicator
    have hijval : i.val < j.val := hij
    simp only [if_pos hij]
    split_ifs <;> norm_num <;> omega
  · have hnot : ¬i.val < j.val := hij
    simp [ZeroGap.inversionTerm, inversionIndicator, crossPairIndicator, hij, hnot]

/-- Formula (24), first for the canonical clockwise representative of any permutation. -/
theorem clockwise_inversion_count (p : State n) :
    (LiftedModel.inversionCount (clockwiseRepresentative p) : ℤ)=
      ((descendingPositions p).card : ℤ)*((n : ℤ)-(descendingPositions p).card)+
        (inversionNumber p : ℤ)-2*leftDepth p := by
  have hcast : (LiftedModel.inversionCount (clockwiseRepresentative p) : ℤ)=
      ∑ i, ∑ j, (ZeroGap.inversionTerm (clockwiseRepresentative p) i j : ℤ) := by
    simp only [LiftedModel.inversionCount, ZeroGap.inversionTerm, Nat.cast_sum]
  rw [hcast]
  simp_rw [clockwise_inversion_term, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [sum_inversion_indicator, sum_cross_pair_indicator, weighted_inversion_balance]
  ring


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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]









/-- A lower displacement bound controls every token's backward exchanges. -/
theorem backward_depth_le_strip {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (h : ℤ) (hlo : ∀ i, -h ≤ d i) (i : Fin n) :
    (backwardDepth d i : ℤ) ≤ h := by
  obtain ⟨a,hmax,he⟩ := exists_depth_extreme hd
  have hh : (backwardDepth d i : ℤ) ≤ backwardDepth d a := by exact_mod_cast hmax i
  have := hlo a
  omega




end LX.AffineScan

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem shifted_lift_permutation_modEq {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ) (i : Fin n) :
    Int.ModEq (n : ℤ) ((i : ℤ)+d i+h) (shiftedLiftPermutation p c h i : ℤ) := by
  apply (LiftedModel.cast_eq_iff_modEq _ _).mp
  have hi := AffineLift.lift_residue hd i
  simp only [Int.cast_add, Int.cast_natCast, Fin.cast_val_eq_self]
  change i+(d i : Fin n)+(h : Fin n)=p.symm i+((c+h : ℤ) : Fin n)
  rw [Int.cast_add, hi, add_assoc]

/-- Translating all endpoints does not change the affine inversion price. -/
theorem inversion_count_translate (F : Fin n → ℤ) (h : ℤ) :
    LiftedModel.inversionCount (fun i => F i+h)=LiftedModel.inversionCount F := by
  simp only [LiftedModel.inversionCount, add_sub_add_right_eq_sub]

/-- Formula (24) for the actual input lift; the finite permutation is derived from it. -/
theorem shifted_lift_inversion_formula {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) :
    (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h)+(inversionNumber (shiftedLiftPermutation p c h) : ℤ)-
        2*leftDepth (shiftedLiftPermutation p c h) := by
  let q := shiftedLiftPermutation p c h
  have hmod := shifted_lift_permutation_modEq hd h
  have heq : (fun i : Fin n => (i : ℤ)+d i+h)=clockwiseRepresentative q :=
    clockwise_representative_unique q _
      (fun i => by have := hband i; omega) hmod
  have hc := shifted_balanced_descending_count q d h hd.1 hband hmod
  have hf := clockwise_inversion_count q
  rw [← heq, inversion_count_translate, hc] at hf
  exact hf

/-- The non-strict capacity bound, with an arbitrary valid strip shift. -/
theorem shifted_lift_inversion_capacity {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) :
    (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      h*((n : ℤ)-h-1) := by
  have hf := shifted_lift_inversion_formula hd h hband
  have hc := shifted_balanced_descending_count (shiftedLiftPermutation p c h) d h
    hd.1 hband (shifted_lift_permutation_modEq hd h)
  have hr := leftDepth_inversion_deficit (shiftedLiftPermutation p c h)
  rw [hc] at hr
  nlinarith





end LX.Core.FiniteCuts

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

/-- The same height controls the exchanges and the largest number of backward moves. -/
theorem candidate_price_components (p : State n) (a : Fin n) :
    (inversions (_root_.LX.AnchoredPhases.displacement p a) : ℤ) ≤ (height p a : ℤ)*(n-height p a-1) ∧
      ∀ i, (backwardDepth (_root_.LX.AnchoredPhases.displacement p a) i : ℤ) ≤ height p a := by
  constructor
  · have h := shifted_lift_inversion_capacity (is_lift p a) (height p a : ℤ) (displacement_band p a)
    exact h
  · intro i
    apply backward_depth_le_strip (is_lift p a) (height p a : ℤ)
    intro j
    have h := (displacement_band p a j).1
    omega










end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]



theorem clockwise_difference_value (q : State n) (i : Fin n) :
    clockwiseRepresentative q i-(i : ℤ)=((q i-i : Fin n) : ℤ) := by
  have hb := clockwise_representative_bounds q i
  have hc := LX.Core.AffineLift.cast_eq_of_modEq (clockwise_representative_modEq q i)
  have hm : ((clockwiseRepresentative q i-(i : ℤ) : ℤ) : Fin n)=q i-i := by
    simp only [Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,hc]
  have hh := congrArg (fun x : Fin n => (x : ℤ)) hm
  simp only [Fin.val_intCast] at hh
  rw [Int.emod_eq_of_lt (by omega) (by omega),Int.toNat_of_nonneg (by omega)] at hh
  exact hh














end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem displacement_offset (p : State n) (a i : Fin n) :
    _root_.LX.AnchoredPhases.displacement p a i=(cyclicOffset p a i : ℤ)-height p a := by
  unfold _root_.LX.AnchoredPhases.displacement
  rw [clockwise_difference_value]
  have he : permutation p a i-i=cyclicOffset p a i := by
    change p i+(a-p a)-i=p i-i-(p a-a)
    abel
  rw [he]







theorem displacement_strict_width (p : State n) (a i j : Fin n) :
    _root_.LX.AnchoredPhases.displacement p a i-_root_.LX.AnchoredPhases.displacement p a j < (n : ℤ) := by
  have hi := displacement_band p a i
  have hj := displacement_band p a j
  omega










end LX.AnchoredPhases

end

section
namespace LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



@[simp] theorem mem_fixedPositions (p : State n) (i : Fin n) :
    i ∈ fixedPositions p ↔ p i=i := by simp [fixedPositions]









end LX.Core.FiniteCuts

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem top_depth_count_eq_fixed (p : State n) (a : Fin n) :
    depthCount (_root_.LX.AnchoredPhases.displacement p a) (height p a)=(fixedPositions (permutation p a)).card := by
  unfold depthCount fixedPositions
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hh : backwardDepth (_root_.LX.AnchoredPhases.displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  rw [← depth_eq_height_iff_fixed]
  omega



end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The next-depth count is bounded uniformly by the largest fixed fiber,
without any majorization or exchange-reserve assumption. -/
theorem solution (p : State n) (h F : ℕ)
    (hall : ∀ a,height p a=h)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hh : 0 < h) (a : Fin n) :
    depthCount (_root_.LX.AnchoredPhases.displacement p a) (h-1) ≤ 2*F+1 := by
  classical
  have htop : depthCount (_root_.LX.AnchoredPhases.displacement p a) h ≤ F := by
    rw [← hall a,top_depth_count_eq_fixed]
    exact hF a
  have hsub : Finset.univ.filter (fun i => h-1 ≤ backwardDepth (_root_.LX.AnchoredPhases.displacement p a) i) ⊆
      Finset.univ.filter (fun i => (cyclicOffset p a i).val < F+2) := by
    intro i hi
    have hdepth := (Finset.mem_filter.mp hi).2
    have hw := displacement_depth_width_bound (is_lift p a)
      (fun i j => (displacement_strict_width p a i j).le) (h-1) i hdepth
    rw [show h-1+1=h by omega,displacement_offset,hall a] at hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  have hc := Finset.card_le_card hsub
  have hb := constant_height_below_count p h F hall hF a (F+2) (by omega)
  change depthCount (_root_.LX.AnchoredPhases.displacement p a) (h-1) ≤ belowCount p a (F+2) at hc
  omega
