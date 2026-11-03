-- Prove2me | solution 1 for LX.AnchoredPhases.conjecture_unpaid_rank_geometry
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:28:51.980429+00:00
-- url     : https://prove2.me/submissions/97eaf5d8-3564-44cc-8e5b-95d43580f2a4

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
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PermutationCode
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RankPeakCount
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SecondExcess
import Definitions.Def_LX_Small4
import Definitions.Def_LX_Small5
import Definitions.Def_LX_Small6
import Definitions.Def_LX_StrictBandInversionCapacity
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapInversionTerms
import Theorems.Thm_LX_AffineScan_displacement_add_depth_le_count
import Theorems.Thm_LX_AffineScan_exists_depth_extreme
import Theorems.Thm_LX_AffineScan_exists_head_with_count
import Theorems.Thm_LX_AffineScan_word_with_nonmaximal_head
import Theorems.Thm_LX_AnchoredPhases_conjecture_unpaid_minimum
import Theorems.Thm_LX_AnchoredPhases_conjecture_window_terminal_threshold
import Theorems.Thm_LX_AnchoredPhases_even_fixed_gap_exact_word
import Theorems.Thm_LX_AnchoredPhases_gap_separation_bounds_fixed
import Theorems.Thm_LX_AnchoredPhases_global_rank_peak_reserve
import Theorems.Thm_LX_AnchoredPhases_low_forward_depth_paid
import Theorems.Thm_LX_AnchoredPhases_low_offset_count_of_forward_payment
import Theorems.Thm_LX_AnchoredPhases_minimum_count_minus_high_count
import Theorems.Thm_LX_AnchoredPhases_minimum_height_ranks
import Theorems.Thm_LX_AnchoredPhases_odd_fixed_gap_exact_word
import Theorems.Thm_LX_AnchoredPhases_rank_peak_anchor_bounds
import Theorems.Thm_LX_AnchoredPhases_rank_peak_next_depth
import Theorems.Thm_LX_AnchoredPhases_rank_peak_next_depth_fiber
import Theorems.Thm_LX_AnchoredPhases_second_excess_count
import Theorems.Thm_LX_AnchoredPhases_smaller_gap_bounds_fixed
import Theorems.Thm_LX_AnchoredPhases_zero_surplus_count_eq_minimum_offsets
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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.PairCore
end LX.PairCore
namespace LX.Small4
end LX.Small4
namespace LX.Small5
end LX.Small5
namespace LX.Small6
end LX.Small6
namespace List
end List

section
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u

theorem ite_eq_left {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h

theorem ite_eq_right {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := if_neg h

end LX

namespace List
universe u

end List

/-
The following proof is adapted from Mathlib, copyright (c) 2026 Seewoo Lee,
licensed under Apache 2.0. Source revision 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Order/Floor/BigOperators.lean, lines 28-45.
-/
namespace Int
open scoped BigOperators


end Int

end

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





theorem energy_cast {n : ℕ} (d : Fin n → ℤ) :
    (energy d : ℤ) = ∑ i, d i ^ 2 := by
  simp [energy, sq_abs]

theorem canonical_lift {n : ℕ} (p : State n) :
    IsLift p 0 (fun i => (p.symm i : ℤ) - (i : ℤ)) := by
  constructor
  · rw [Finset.sum_sub_distrib]
    have h := Equiv.sum_comp p.symm (fun i : Fin n => (i : ℤ))
    rw [h]
    simp
  · intro i
    simp [Int.ModEq]





theorem shift_balanced {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n))
    (hd : ∑ i, d i = 0) : ∑ i, phaseShift d s i = 0 := by
  simp [phaseShift, Finset.sum_sub_distrib, Finset.sum_add_distrib, hd,
    Finset.sum_ite_mem, mul_comm]

theorem shift_lift {n : ℕ} {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (s : Finset (Fin n)) :
    IsLift p (c + s.card) (phaseShift d s) := by
  refine ⟨shift_balanced d s hd.1, ?_⟩
  intro i
  have h := (hd.2 i).add_right (s.card : ℤ)
  simp only [phaseShift]
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi]
    rw [← add_sub_assoc, Int.sub_modulus_modEq_iff]
    simpa only [add_assoc] using h
  · simp only [ite_eq_right hi, sub_zero]
    simpa only [add_assoc] using h

/-- The exact change in quadratic energy for every subset, not just sorted prefixes. -/
theorem shift_energy {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n))
    (hd : ∑ i, d i = 0) :
    (energy (phaseShift d s) : ℤ) - energy d =
      (n : ℤ) * ((s.card : ℤ) * (n - s.card) - 2 * ∑ i ∈ s, d i) := by
  rw [energy_cast, energy_cast]
  have point (i : Fin n) : phaseShift d s i ^ 2 =
      d i ^ 2 + 2 * (s.card : ℤ) * d i + (s.card : ℤ) ^ 2 +
      if i ∈ s then (n : ℤ)^2 - 2*n*s.card - 2*n*d i else 0 := by
    unfold phaseShift
    split_ifs <;> ring
  simp_rw [point]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_mem, hd]
  ring



theorem minimal_majorized {n : ℕ} (hn : 0 < n) {p : State n} {c : ℤ}
    {d : Fin n → ℤ} (hd : IsLift p c d)
    (hmin : ∀ c' d', IsLift p c' d' → energy d ≤ energy d') : Majorized d := by
  intro s
  have h := hmin _ _ (shift_lift hd s)
  have he : (energy d : ℤ) ≤ energy (phaseShift d s) := by exact_mod_cast h
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hprod : 0 ≤ (n : ℤ) *
      ((s.card : ℤ) * (n - s.card) - 2 * ∑ i ∈ s, d i) := by
    rw [← shift_energy d s hd.1]
    omega
  have hnonneg := nonneg_of_mul_nonneg_right hprod hn'
  omega






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
/-! Exact subset capacity for injective integer coordinates in a finite
interval. The endpoints need not be consecutive. -/
namespace LX.Core.FiniteCoordinates
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem range_sum_twice (k : ℕ) : 2*(∑ i ∈ Finset.range k, (i : ℤ))=(k : ℤ)*(k-1) := by
  by_cases hk : k=0
  · simp [hk]
  · have h := Finset.sum_range_id_mul_two k
    have hz := congrArg (fun a : ℕ => (a : ℤ)) h
    push_cast at hz
    rw [Nat.cast_sub (by omega : 1 ≤ k)] at hz
    norm_num at hz
    nlinarith


end LX.Core.FiniteCoordinates

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
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]


theorem raw_offset_mass (p : State n) :
    (∑ i : Fin n,((p i-i : Fin n) : ℤ))=(n : ℤ)*(descendingPositions p).card := by
  have h := clockwise_representative_mass p
  simpa only [clockwise_difference_value] using h


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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem anchor_reserve_nonneg (p : State n) (a : Fin n) : 0 ≤ anchorReserve p a := by
  have hh := (candidate_price_components p a).1
  unfold anchorReserve
  omega
















end LX.AnchoredPhases

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]









/-- Majorization bounds the number of coordinates below any fixed threshold. -/
theorem majorized_lower_threshold {d : Fin n → ℤ}
    (hb : ∑ i,d i=0) (hm : LX.Core.AffineLift.Majorized d)
    (S : Finset (Fin n)) (t : ℤ) (ht : 2*t ≤ (n : ℤ))
    (hS : ∀ i ∈ S, d i ≤ -t) : (S.card : ℤ) ≤ (n : ℤ)-2*t := by
  have hmaj := LX.Core.AffineLift.majorized_neg hb hm S
  have hs : (S.card : ℤ)*t ≤ ∑ i ∈ S, -d i := by
    calc
      _ = ∑ _i ∈ S, t := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by have := hS i hi; omega)
  by_cases he : S.card=0
  · simp only [he,Nat.cast_zero]
    omega
  · have hp : (0 : ℤ)<S.card := by exact_mod_cast Nat.pos_of_ne_zero he
    nlinarith

/-- Only a bounded number of tokens can have near-maximal depth. The bound
uses the next level, so it can be iterated down from the largest depth. -/
theorem depth_count_recurrence {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (hm : LX.Core.AffineLift.Majorized d)
    (k : ℕ) (hk : 2*k ≤ n) :
    (depthCount d k : ℤ) ≤ (n : ℤ)-2*k+2*depthCount d (k+1) := by
  have hh : (depthCount d k : ℤ) ≤ (n : ℤ)-2*((k : ℤ)-depthCount d (k+1)) := by
    apply majorized_lower_threshold hd.1 hm _ ((k : ℤ)-depthCount d (k+1))
    · omega
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hb := displacement_add_depth_le_count hd hm k i hi'
      omega
  linarith

theorem top_depth_count {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (hm : LX.Core.AffineLift.Majorized d)
    (h : ℕ) (hh : 2*h ≤ n) (hmax : ∀ i, backwardDepth d i ≤ h) :
    (depthCount d h : ℤ) ≤ (n : ℤ)-2*h := by
  have hz : depthCount d (h+1)=0 := by
    unfold depthCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    have := hmax i
    omega
  have hc := depth_count_recurrence hd hm h hh
  simpa only [hz,Nat.cast_zero,mul_zero,add_zero] using hc




end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]





/-- Majorization pays the initial prefix using only the highest depth count.
The exchange count is left exact for subsequent arithmetic payment. -/
theorem majorized_exchange_reserve_word (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) (hm : Majorized d)
    (h : ℕ) (hh : 0 < h) (hhalf : 2*h ≤ n)
    (hmax : ∀ i,backwardDepth d i ≤ h) :
    ∃ w : List Letter,p*eval w=1 ∧
      (w.length : ℤ) ≤ inversions d+(h : ℤ)*((n : ℤ)-3)+2*n-2 := by
  obtain ⟨r,hr,hhead⟩ := exists_head_with_count d h hh
  have hc := top_depth_count hd hm h hhalf hmax
  obtain ⟨w,hw,hlen⟩ := word_with_nonmaximal_head hn p c d hd h r hmax hhead
  refine ⟨w,hw,?_⟩
  have hrc : (r.val : ℤ) ≤ (n : ℤ)-2*h := by omega
  nlinarith



end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases

namespace LX


end LX

end

section
/-! A constructive enumeration of permutations. Checking one word per code
avoids a quadratic search through a finite set of evaluated words. -/
namespace LX.Core









@[simp] theorem decode_encode {n : ℕ} (p : State n) : decode (encode p) = p := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [encode, decode, ih, Prod.mk.eta, Equiv.symm_apply_apply]




end LX.Core

end

section
namespace LX

theorem words_of_code_certificate {n B : ℕ} [NeZero n]
    (table : LX.Core.PermCode n → List Letter)
    (checked : ∀ c,eval (table c)=LX.Core.decode c ∧ (table c).length ≤ B) :
    ∀ p : State n,∃ w : List Letter,eval w=p ∧ w.length ≤ B := by
  intro p
  obtain ⟨he,hl⟩ := checked (LX.Core.encode p)
  exact ⟨table (LX.Core.encode p),by simpa using he,hl⟩

end LX

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
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem offset_difference_mass (p : State n) (a : Fin n) :
    (∑ i : Fin n, ((p i-i-(p a-a) : Fin n) : ℤ))=(n : ℤ)*height p a := by
  have hm := clockwise_representative_mass (permutation p a)
  simp_rw [clockwise_difference_value] at hm
  have he (i : Fin n) : permutation p a i-i=p i-i-(p a-a) := by
    change p i+(a-p a)-i=p i-i-(p a-a)
    abel
  simpa only [he,height] using hm


end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem cyclic_subtraction_value (u v : Fin n) :
    ((u-v : Fin n) : ℤ)=(u : ℤ)-(v : ℤ)+if u.val < v.val then (n : ℤ) else 0 := by
  have hu := u.isLt
  have hv := v.isLt
  change (((u-v).val : ℕ) : ℤ)=_
  rw [Fin.val_sub]
  by_cases h : u.val < v.val
  · rw [Nat.mod_eq_of_lt (by omega : n-v.val+u.val < n),ite_eq_left h]
    omega
  · have he : n-v.val+u.val=n+(u.val-v.val) := by omega
    rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega : u.val-v.val < n),ite_eq_right h]
    omega



theorem cyclic_offset_mass (p : State n) (a : Fin n) :
    (∑ i : Fin n, (cyclicOffset p a i : ℤ))=(n : ℤ)*height p a :=
  offset_difference_mass p a









theorem rank_surplus_nonnegative (p : State n) (a : Fin n)
    (hmin : ∀ b, height p a ≤ height p b) (t : ℕ) (ht : t ≤ n) :
    0 ≤ rankSurplus p a t := by
  have hh := minimum_height_ranks p a hmin t ht
  unfold rankSurplus
  omega

theorem above_threshold_card (r : Fin n) :
    (∑ t : Fin n, if r.val < t.val then (1 : ℤ) else 0)=(n : ℤ)-1-(r : ℤ) := by
  have he : Finset.univ.filter (fun t : Fin n => r.val < t.val)=Finset.Ioi r := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ioi,Fin.lt_def]
  have hc : (Finset.univ.filter (fun t : Fin n => r.val < t.val)).card=n-1-r.val := by
    rw [he,Fin.card_Ioi]
  have hsum : (∑ t : Fin n, if r.val < t.val then (1 : ℤ) else 0)=
      ((Finset.univ.filter (fun t : Fin n => r.val < t.val)).card : ℤ) := by simp
  rw [hsum,hc]
  have hh := r.isLt
  omega

theorem below_count_sum (p : State n) (a : Fin n) :
    (∑ t : Fin n, (belowCount p a t.val : ℤ))=(n : ℤ)*((n : ℤ)-1-height p a) := by
  simp only [belowCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  simp_rw [above_threshold_card]
  rw [Finset.sum_sub_distrib,cyclic_offset_mass]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Exact total rank surplus. In the remaining height cases it is at most 2n. -/
theorem rank_surplus_sum (p : State n) (a : Fin n) :
    2*(∑ t : Fin n, rankSurplus p a t.val)=
      (n : ℤ)*((n : ℤ)-1-2*height p a) := by
  simp only [rankSurplus,Finset.sum_sub_distrib]
  rw [below_count_sum]
  have htri : 2*(∑ t : Fin n, (t : ℤ))=(n : ℤ)*((n : ℤ)-1) := by
    rw [Fin.sum_univ_eq_sum_range]
    exact LX.Core.FiniteCoordinates.range_sum_twice n
  nlinarith










end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem global_minimum_majorized {p : State n} {a : Fin n} (h : GlobalMinimum p a) :
    Majorized (_root_.LX.AnchoredPhases.displacement p a) :=
  minimal_majorized (NeZero.pos n) (is_lift p a) h













end LX.AnchoredPhases

end

section
-- Generated witnesses; the Lean kernel checks semantics, coverage and length.
namespace LX.Small4
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem checked : ∀ c : LX.Core.PermCode 4,
    eval (table c)=LX.Core.decode c ∧ (table c).length ≤ 7 := by
  decide +kernel

theorem sharp_words (p : State 4) :
    ∃ w : List Letter,eval w=p ∧ w.length ≤ 7 :=
  words_of_code_certificate table checked p



end LX.Small4

end

section
-- Generated witnesses; the Lean kernel checks semantics, coverage and length.
namespace LX.Small5
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem checked : ∀ c : LX.Core.PermCode 5,
    eval (table c)=LX.Core.decode c ∧ (table c).length ≤ 11 := by
  decide +kernel

theorem sharp_words (p : State 5) :
    ∃ w : List Letter,eval w=p ∧ w.length ≤ 11 :=
  words_of_code_certificate table checked p



end LX.Small5

end

section
-- Generated witnesses; the Lean kernel checks semantics, coverage and length.
namespace LX.Small6
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem checked : ∀ c : LX.Core.PermCode 6,
    eval (table c)=LX.Core.decode c ∧ (table c).length ≤ 18 := by
  decide +kernel

theorem sharp_words (p : State 6) :
    ∃ w : List Letter,eval w=p ∧ w.length ≤ 18 :=
  words_of_code_certificate table checked p



end LX.Small6

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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem conjecture_small_word (hn4 : 4 ≤ n) (hn6 : n ≤ 6) (p : State n)
    (m e : ℕ) (he : e ≤ 1) (hn : n=2*m+e) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ)) := by
  have hc : n=4 ∨ n=5 ∨ n=6 := by omega
  rcases hc with rfl | rfl | rfl
  · obtain ⟨w,hw,hprice⟩ := LX.Small4.sharp_words p⁻¹
    exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
  · obtain ⟨w,hw,hprice⟩ := LX.Small5.sharp_words p⁻¹
    exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
  · obtain ⟨w,hw,hprice⟩ := LX.Small6.sharp_words p⁻¹
    exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩




end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The height at any threshold, including an unoccupied one, is its
shifted offset mass. -/
theorem shifted_offset_rank_mass (p : State n) (a t : Fin n) :
    (∑ i : Fin n, ((cyclicOffset p a i-t : Fin n) : ℤ))=
      (n : ℤ)*((height p a : ℤ)+rankSurplus p a t.val) := by
  have hc : (∑ i : Fin n,if (cyclicOffset p a i).val < t.val then (n : ℤ) else 0)=
      (n : ℤ)*belowCount p a t.val := by
    rw [← Finset.sum_filter]
    simp [belowCount,mul_comm]
  simp_rw [cyclic_subtraction_value]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,cyclic_offset_mass,hc]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,rankSurplus]
  ring









theorem rank_peak_descending_count (p : State n) (a : Fin n) (R : ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R) :
    (descendingPositions p).card ≤ height p a+R := by
  let t : Fin n := -(p a-a)
  have hm := shifted_offset_rank_mass p a t
  have he (i : Fin n) : cyclicOffset p a i-t=p i-i := by dsimp [cyclicOffset,t]; ring
  simp_rw [he] at hm
  rw [raw_offset_mass] at hm
  have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hr := hR t
  nlinarith




end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]





/-- Choose a least gap in a prescribed height class and terminal range.
The fallback is irrelevant when that class is empty. -/
theorem exists_least_gap_above (p : State n) (h J : ℕ) :
    ∃ b : Fin n,∀ c,height p c=h → J ≤ (c-p c).val →
      height p b=h ∧ J ≤ (b-p b).val ∧ (b-p b).val ≤ (c-p c).val := by
  classical
  let S := Finset.univ.filter fun c : Fin n => height p c=h ∧ J ≤ (c-p c).val
  by_cases hs : S.Nonempty
  · obtain ⟨b,hb,hmin⟩ := Finset.exists_min_image S (fun c => (c-p c).val) hs
    have hb' := (Finset.mem_filter.mp hb).2
    exact ⟨b,fun c hc hg => ⟨hb'.1,hb'.2,hmin c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,hg⟩)⟩⟩
  · exact ⟨0,fun c hc hg => False.elim (hs ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,hg⟩⟩)⟩





end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



/-- Critical parity cases spend a quadratic amount of the actual reserve. -/
theorem critical_rank_peak_reserve (p : State n) (a t : Fin n)
    (ha : GlobalMinimum p a) (e : ℕ) (hn : n=2*height p a+2+e) :
    rankSurplus p a t.val*(rankSurplus p a t.val-1-e) ≤ anchorReserve p a := by
  have hh := global_rank_peak_reserve p a t ha
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2+e := by exact_mod_cast hn
  rw [hn'] at hh
  convert hh using 1
  ring



end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]
set_option maxHeartbeats 500000
/-- Necessary conditions for a counterexample to the conjectured parity bounds.
This is a reduction, not an assertion that those conditions are impossible. -/
theorem solution (hn4 : 4 ≤ n) (p : State n)
    (m e : ℕ) (he : e ≤ 1) (hn : n=2*m+e)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ))) :
    ∃ a r : Fin n,∃ R : ℕ,6 < n ∧ GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ b,height p a ≤ height p b) ∧ 0 < R ∧ R+2*e ≤ 8 ∧
      rankSurplus p a r.val=R ∧ (∀ t : Fin n,rankSurplus p a t.val ≤ R) ∧
      secondExcess p a ≤ (2*(R : ℤ)+1+(R+2-(e*m+3) : ℕ)) := by
  classical
  have hnlarge : 6 < n := by
    by_contra hnot
    exact hunpaid (conjecture_small_word hn4 (by omega) p m e he hn)
  obtain ⟨a,ha,hh,hmin⟩ := conjecture_unpaid_minimum hn4 p m e he hn hunpaid
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun t => rankSurplus p a t.val) ⟨0,Finset.mem_univ _⟩
  have hr0 := rank_surplus_nonnegative p a hmin r.val (Nat.le_of_lt r.isLt)
  let R := (rankSurplus p a r.val).toNat
  have hpeak : rankSurplus p a r.val=R := by dsimp [R]; rw [Int.toNat_of_nonneg hr0]
  have hR (t : Fin n) : rankSurplus p a t.val ≤ R := by
    rw [← hpeak]
    exact hr t (Finset.mem_univ _)
  have hRpos : 0 < R := by
    by_contra hnot
    have hz (t : Fin n) : rankSurplus p a t.val=0 := by
      have hi := hR t
      have hlo := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
      omega
    have hs := rank_surplus_sum p a
    simp_rw [hz] at hs
    simp only [Finset.sum_const_zero,mul_zero] at hs
    interval_cases e <;>
      have hn' : (n : ℤ)=2*(height p a : ℤ)+2 ∨ (n : ℤ)=2*(height p a : ℤ)+3 := by omega
    all_goals rcases hn' with hn' | hn' <;> nlinarith
  have hb := rank_peak_anchor_bounds p a R hmin hR
  obtain ⟨z,hz⟩ := exists_least_gap_above p m (R+1)
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  let P := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  have hquad : ((R : ℤ)-1)*(R-2) ≤ 2*(Z.card : ℤ)-2*(P.card : ℤ)+
      (n : ℤ)*((n : ℤ)-3-2*height p a) :=
    minimum_count_minus_high_count p a r R hmin hRpos hpeak
  let Dlow := (descendingPositions p).filter fun b => height p b=height p a
  let Dhigh := (descendingPositions p).filter fun b => height p b=m
  obtain ⟨b,hbmem,hbgap⟩ := Finset.exists_min_image
    (Finset.univ.filter fun b : Fin n => height p b=height p a) (fun b => (b-p b).val)
    ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have hbh : height p b=height p a := (Finset.mem_filter.mp hbmem).2
  obtain ⟨v,hv⟩ := exists_least_gap_above p (height p a) (R+2)
  let E := ({(b-p b).val} ∪ {(v-p v).val}) ∪ Finset.Ico (e*m+3) (R+2)
  have hE : E.card ≤ 2+(R+2-(e*m+3)) := by
    have hc : E.card ≤ (({(b-p b).val} ∪ {(v-p v).val}) : Finset ℕ).card+
        (Finset.Ico (e*m+3) (R+2)).card := Finset.card_union_le _ _
    have hp := Finset.card_union_le {(b-p b).val} {(v-p v).val}
    simp only [Finset.card_singleton,Nat.card_Ico] at hc hp
    omega
  let Hlow : ℕ := if height p 0=height p a then 1 else 0
  let Hhigh : ℕ := if height p 0=m then 1 else 0
  have hheads : Hlow+Hhigh ≤ 1 := by
    dsimp [Hlow,Hhigh]
    split_ifs <;> omega
  have hlow : Z.card ≤ Dlow.card+E.card+Hlow := by
    have hc := low_offset_count_of_forward_payment p (height p a) E hunpaid (by
      intro c hch hgap hhead hlast hback
      by_cases hsmall : (c-p c).val < e*m+3
      · have hle := hbgap c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hch⟩)
        have hne : (c-p c).val ≠ (b-p b).val := by
          intro heq
          apply hgap
          simp [E,heq]
        have hf := smaller_gap_bounds_fixed p c b (by omega) (by omega)
        have hr := anchor_reserve_nonneg p c
        interval_cases e
        · obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p c (by omega) (by omega) (by omega)
          exact ⟨w,hw,by omega⟩
        · obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p c (by omega) (by omega) (by omega)
          exact ⟨w,hw,by omega⟩
      · have hglow : R+2 ≤ (c-p c).val := by
          by_contra hnot
          exact hgap (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))
        have hv' := hv c hch hglow
        have hne : (c-p c).val ≠ (v-p v).val := by
          intro heq
          apply hgap
          simp [E,heq]
        have hf := gap_separation_bounds_fixed p c v (by omega) (by omega)
        have hd := rank_peak_next_depth_fiber p a R hR c (by omega)
        obtain ⟨w,hw,hprice⟩ := low_forward_depth_paid p c (by omega)
          (by interval_cases e <;> omega) hhead hlast hback (by omega) (by omega)
        exact ⟨w,hw,by omega⟩)
    rw [← zero_surplus_count_eq_minimum_offsets p a hmin] at hc
    exact hc
  have hupper : e*m+2 < n := by interval_cases e <;> omega
  let I := Finset.Icc (R+1) (e*m+2)
  let W := I.image (fun g : ℕ => -(g : Fin n))
  have hWcard : W.card=I.card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj he
    have hi' := (Finset.mem_Icc.mp hi).2
    have hj' := (Finset.mem_Icc.mp hj).2
    have hij : (i : Fin n)=(j : Fin n) := neg_injective he
    have hiv : (i : Fin n).val=i := Nat.mod_eq_of_lt (by omega)
    have hjv : (j : Fin n).val=j := Nat.mod_eq_of_lt (by omega)
    have hv := congrArg Fin.val hij
    omega
  have hWlower : (e*m : ℕ)+2-(R : ℤ) ≤ W.card := by
    rw [hWcard]
    dsimp only [I]
    rw [Nat.card_Icc]
    omega
  let Bad := P.image (fun t => p a-a+t)
  let V := Dhigh.image (fun b => p b-b)
  have hBad : Bad.card ≤ P.card := Finset.card_image_le
  have hV : V.card ≤ Dhigh.card := Finset.card_image_le
  let Head : Finset (Fin n) := if height p 0=m then {p 0} else ∅
  have hHead : Head.card=Hhigh := by dsimp [Head,Hhigh]; split_ifs <;> simp
  have hsub : W ⊆ (Bad ∪ Head) ∪ (V ∪ {p z-z}) := by
    intro t ht
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ht
    have hg' := Finset.mem_Icc.mp hg
    have ht := conjecture_window_terminal_threshold p a z m R g e he hn hnlarge hupper hh hmin hb.2 hR hz hunpaid
      hg'.1 hg'.2
    rcases ht with hhigh | hhead | hspecial | ⟨b,hb,hbh,hbr⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨-(g : Fin n)-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
      ring
    · apply Finset.mem_union_left
      simp [Head,hhead.1,hhead.2]
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_singleton.mpr hspecial
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨hb,hbh⟩,hbr⟩
  have hwindow : W.card ≤ P.card+Hhigh+1+Dhigh.card := by
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le (Bad ∪ Head) (V ∪ {p z-z}))
    have hB := Finset.card_union_le Bad Head
    rw [hHead] at hB
    have hVextra := Finset.card_union_le V {p z-z}
    simp only [Finset.card_singleton] at hVextra
    omega
  have hdisjoint : Disjoint Dlow Dhigh := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    omega
  have hsubset : Dlow ∪ Dhigh ⊆ descendingPositions p := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (Finset.mem_filter.mp hb).1
    · exact (Finset.mem_filter.mp hb).1
  have hsum := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisjoint] at hsum
  have hdesc := rank_peak_descending_count p a R hR
  have hlinear : (Z.card : ℤ)-(P.card : ℤ) ≤
      (m : ℤ)-(e*m : ℕ)+2*(R : ℤ)+(E.card : ℤ)-1 := by omega
  have hquad' : ((R : ℤ)-1)*(R-2) ≤ 4*(R : ℤ)+2*E.card-2 := by
    interval_cases e
    · simp only [Nat.zero_mul, Nat.cast_zero, sub_zero] at hlinear
      have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
      have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
      nlinarith only [hquad,hlinear,hn',hm']
    · simp only [Nat.one_mul] at hlinear
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith only [hquad,hlinear,hn']
  have hheight : (height p a : ℤ)+R ≤ (n : ℤ)-1 := by
    have hm := shifted_offset_rank_mass p a r
    have hs : (∑ i : Fin n,((cyclicOffset p a i-r : Fin n) : ℤ)) ≤
        (n : ℤ)*((n : ℤ)-1) := by
      calc
        _ ≤ ∑ _i : Fin n,((n : ℤ)-1) := by
          apply Finset.sum_le_sum
          intro i _
          have := (cyclicOffset p a i-r).isLt
          omega
        _ = _ := by simp; ring
    rw [hm,hpeak] at hs
    have hnpos : (0 : ℤ) < n := by omega
    nlinarith only [hs,hnpos]
  have hRbound : R+e ≤ 8 := by
    interval_cases e
    · simp only [Nat.zero_mul] at hE
      have hE' : (E.card : ℤ) ≤ (R : ℤ)+1 := by omega
      by_contra hnot
      have hr : (9 : ℤ) ≤ R := by omega
      nlinarith only [hquad',hE',hr,mul_nonneg (by omega : (0 : ℤ) ≤ R)
        (by omega : (0 : ℤ) ≤ (R : ℤ)-9)]
    · simp only [Nat.one_mul] at hE
      have hE' : (E.card : ℤ) ≤ 2 := by omega
      by_contra hnot
      have hr : (8 : ℤ) ≤ R := by omega
      nlinarith only [hquad',hE',hr,mul_nonneg (by omega : (0 : ℤ) ≤ R)
        (by omega : (0 : ℤ) ≤ (R : ℤ)-7)]
  have hQ : secondExcess p a ≤ (2*(R : ℤ)+1+(R+2-(e*m+3) : ℕ)) := by
    have hc := second_excess_count p a hmin
    change 2*secondExcess p a=2*(Z.card : ℤ)-2*P.card+
      (n : ℤ)*((n : ℤ)-3-2*height p a) at hc
    have hE' : (E.card : ℤ) ≤ 2+((R+2-(e*m+3) : ℕ) : ℤ) := by exact_mod_cast hE
    interval_cases e
    · simp only [Nat.zero_mul,Nat.cast_zero,sub_zero] at hlinear hE' ⊢
      have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
      have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
      nlinarith only [hc,hlinear,hE',hn',hm']
    · simp only [Nat.one_mul] at hlinear hE' ⊢
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith only [hc,hlinear,hE',hn']
  have hRbound' : R+2*e ≤ 8 := by
    interval_cases e
    · omega
    · by_contra hnot
      have hseven : R=7 := by omega
      have hres := critical_rank_peak_reserve p a r ha 1 (by omega)
      rw [hpeak,hseven] at hres
      norm_num at hres
      have hmlarge : 36 ≤ m := by
        by_contra hsmall
        obtain ⟨w,hw,hprice⟩ := majorized_exchange_reserve_word (by omega : 2 ≤ n)
          p (phase p a) (_root_.LX.AnchoredPhases.displacement p a) (is_lift p a) (global_minimum_majorized ha)
          (height p a) (by omega) (by omega)
          (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
        apply hunpaid
        refine ⟨w,hw,?_⟩
        norm_num
        have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
        have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
        have hm35 : (m : ℤ) ≤ 35 := by omega
        unfold anchorReserve at hres
        nlinarith only [hprice,hres,hn',hm',hm35]
      have hlow' : Z.card ≤ Dlow.card+1+Hlow := by
        have hc := low_offset_count_of_forward_payment p (height p a) {(b-p b).val} hunpaid (by
          intro c hch hgap hhead hlast hback
          have hne : (c-p c).val ≠ (b-p b).val := by simpa using hgap
          have hle := hbgap c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hch⟩)
          by_cases hsmall : (c-p c).val < m+3
          · have hf := smaller_gap_bounds_fixed p c b (by omega) (by omega)
            have hr := anchor_reserve_nonneg p c
            obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p c (by omega) (by omega) (by omega)
            exact ⟨w,hw,by norm_num; omega⟩
          · have hd := rank_peak_next_depth p a R hR c (by omega)
            obtain ⟨w,hw,hprice⟩ := low_forward_depth_paid p c (by omega)
              (Or.inr (by omega)) hhead hlast hback (by omega) (by omega)
            exact ⟨w,hw,by norm_num; omega⟩)
        rw [← zero_surplus_count_eq_minimum_offsets p a hmin,Finset.card_singleton] at hc
        exact hc
      have hlinear' : (Z.card : ℤ)-(P.card : ℤ) ≤ 14 := by
        simp only [Nat.one_mul] at hWlower
        omega
      rw [hseven] at hquad
      norm_num at hquad
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith only [hquad,hlinear',hn']
  exact ⟨a,r,R,hnlarge,ha,hh,hmin,hRpos,hRbound',hpeak,hR,hQ⟩
