-- Prove2me | solution 1 for LX.AnchoredPhases.even_unit_exists_one_fixed
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:51:28.990542+00:00
-- url     : https://prove2.me/submissions/c3486c96-8849-4a90-96fc-6eb96b7da397

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
import Definitions.Def_LX_FiniteEnergyRotation
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_FixedPairJoinPrice
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PairCoreGeometry
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PrunedLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_ShallowCutShift
import Definitions.Def_LX_StrictBandInversionCapacity
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoWindowCycleDefect
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_AnchoredPhases_even_unit_reserve_height
import Theorems.Thm_LX_AnchoredPhases_even_unit_two_fixed_next_phase
import Theorems.Thm_LX_AnchoredPhases_minimum_energy_iff_minimum_exchanges
import Theorems.Thm_LX_AnchoredPhases_two_fixed_no_offset_one
import Theorems.Thm_LX_AnchoredPhases_unit_anchor_reserve_rigidity
import Theorems.Thm_LX_Core_AffineLift_majorized_level_count
import Theorems.Thm_LX_Core_AffineLift_short_coordinates
import Theorems.Thm_LX_Core_FiniteCuts_domain_rotation_inversions
import Theorems.Thm_LX_Core_FiniteCuts_inverse_rotate_int
import Theorems.Thm_LX_Core_FiniteCuts_inversion_number_inverse
import Theorems.Thm_LX_Core_FiniteCuts_rotation_energy_change
import Theorems.Thm_LX_Core_FiniteCuts_shifted_support_add_extreme_count
import Theorems.Thm_LX_CycleGeometry_two_fixed_no_neighbor_cycles_are_pairs

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
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace LX.MatchingGeometry
end LX.MatchingGeometry
namespace LX.PairCore
end LX.PairCore
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




















@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]









end LX.Core.AffineLift

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









theorem permutation_anchor (p : State n) (a : Fin n) : permutation p a a = a := by
  simp [permutation]

theorem displacement_balance (p : State n) (a : Fin n) : ∑ i, _root_.LX.AnchoredPhases.displacement p a i = 0 := by
  unfold _root_.LX.AnchoredPhases.displacement
  rw [Finset.sum_sub_distrib, clockwise_representative_mass]
  simp [height]

theorem displacement_band (p : State n) (a i : Fin n) :
    0 ≤ _root_.LX.AnchoredPhases.displacement p a i + height p a ∧ _root_.LX.AnchoredPhases.displacement p a i + height p a < (n : ℤ) := by
  have h := clockwise_representative_bounds (permutation p a) i
  unfold _root_.LX.AnchoredPhases.displacement
  omega

theorem displacement_anchor (p : State n) (a : Fin n) :
    _root_.LX.AnchoredPhases.displacement p a a = -(height p a : ℤ) := by
  simp [_root_.LX.AnchoredPhases.displacement, clockwiseRepresentative, permutation_anchor]



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
namespace LX.MatchingGeometry
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



variable [NeZero n]

theorem eq_add_of_value_add (i j : Fin n) (k : ℕ) (h : i.val+k=j.val) : i+(k : Fin n)=j := by
  have he := congrArg (fun t : ℕ => (t : Fin n)) h
  simpa only [Nat.cast_add,Fin.cast_val_eq_self] using he








end LX.MatchingGeometry

end

section
namespace LX.CycleGeometry
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Even displacement is preserved along every actual cycle, expressed
inside the cyclic additive group so that the seam is handled as well. -/
theorem same_cycle_even_difference (q : State n) (he : ∀ i : Fin n,Even (q i-i))
    (i j : Fin n) (hij : q.SameCycle i j) : Even (j-i) := by
  obtain ⟨k,hk⟩ := hij.exists_nat_pow_eq
  have hp : ∀ k : ℕ,Even ((q^k) i-i) := by
    intro k
    induction k with
    | zero => simpa using (even_zero : Even (0 : Fin n))
    | succ k ih =>
      have hs := (he ((q^k) i)).add ih
      simpa only [pow_succ',Equiv.Perm.mul_apply,sub_add_sub_cancel] using hs
  rw [← hk]
  exact hp k

/-- In even dimension, a cycle whose displacements are even cannot
contain two linearly neighboring physical positions. -/
theorem even_displacement_no_neighbor_cycle (hn2 : 2 ≤ n) (hn : Even n)
    (q : State n) (he : ∀ i : Fin n,Even (q i-i))
    (i j : Fin n) (hij : i.val+1=j.val) : ¬q.SameCycle i j := by
  intro hs
  have hd := same_cycle_even_difference q he i j hs
  have hj : i+1=j := LX.MatchingGeometry.eq_add_of_value_add i j 1 hij
  rw [← hj] at hd
  have hdiff : i+1-i=(1 : Fin n) := by ring
  rw [hdiff] at hd
  have hm := (Fin.even_iff_mod_of_even hn).mp hd
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < n)] at hm

end LX.CycleGeometry

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases

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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem cyclic_offset_reanchor (p : State n) (a b i : Fin n) :
    cyclicOffset p b i=cyclicOffset p a i-cyclicOffset p a b := by
  unfold cyclicOffset
  abel




























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





theorem global_minimum_exchanges {p : State n} {a : Fin n} (ha : GlobalMinimum p a) :
    ∀ b,inversions (_root_.LX.AnchoredPhases.displacement p a) ≤ inversions (_root_.LX.AnchoredPhases.displacement p b) :=
  (minimum_energy_iff_minimum_exchanges p a).mp (fun b => ha _ _ (is_lift p b))







end LX.AnchoredPhases

end

section
namespace LX.PairCore
variable {n : ℕ}






end LX.PairCore

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem majorized_anchor_fixed_positions (p : State n) (a : Fin n)
    (hm : Majorized (_root_.LX.AnchoredPhases.displacement p a)) :
    ((LX.Core.FiniteCuts.fixedPositions (permutation p a)).card : ℤ) ≤ (n : ℤ)-2*height p a := by
  have hh := (short_coordinates (is_lift p a).1 hm a).2
  rw [displacement_anchor] at hh
  have hext := majorized_negative_level_count (is_lift p a).1 hm (height p a : ℤ) (by omega)
  have hs := LX.Core.FiniteCuts.shifted_support_add_extreme_count (is_lift p a)
    (height p a : ℤ) (displacement_band p a)
  rw [shifted_anchor_permutation] at hs
  have hf := LX.Core.FiniteCuts.fixed_positions_card (permutation p a)
  omega


end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]






/-- Exact rank and fixed-point constraints, extracted from the actual input.
The two possible fixed-point counts give one or two units of cycle excess. -/
theorem even_unit_reserve_source {p : State n} {a : Fin n}
    (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (_root_.LX.AnchoredPhases.displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) :
    let q := permutation p a
    LX.Core.FiniteCuts.cycleDefect q=0 ∧
      q.support.card=q.cycleFactorsFinset.card+m ∧
      ((LX.Core.FiniteCuts.fixedPositions q).card=1 ∨
       (LX.Core.FiniteCuts.fixedPositions q).card=2) ∧
      q.support.card=2*q.cycleFactorsFinset.card+
        (LX.Core.FiniteCuts.fixedPositions q).card := by
  obtain ⟨hh,hr⟩ := even_unit_reserve_height m hn ha hunit
  obtain ⟨hz,hrank,_,_,_⟩ := unit_anchor_reserve_rigidity p a
    (global_minimum_majorized ha) hr
  have hf := majorized_anchor_fixed_positions p a (global_minimum_majorized ha)
  have hcard := LX.Core.FiniteCuts.fixed_positions_card (permutation p a)
  have hpos : 0 < (LX.Core.FiniteCuts.fixedPositions (permutation p a)).card := by
    apply Finset.card_pos.mpr
    exact ⟨a,(LX.Core.FiniteCuts.mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
  dsimp only
  exact ⟨hz,by omega,by omega,by omega⟩











end LX.AnchoredPhases

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}







theorem value_rotation_inversions (p : State (k+1)) :
    inversionNumber ((finRotate (k+1))⁻¹*p)+2*(p⁻¹ 0).val=inversionNumber p+k := by
  have h := domain_rotation_inversions p⁻¹
  have he : p⁻¹*finRotate (k+1)=((finRotate (k+1))⁻¹*p)⁻¹ := by simp
  rw [he,inversion_number_inverse,inversion_number_inverse] at h
  exact h



end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]




theorem shift_conjugate_succ (p : State n) (t : ℕ) :
    shiftConjugate p (t+1)=rotateConjugate (shiftConjugate p t) := by
  simp only [shiftConjugate,rotateConjugate,pow_succ,mul_inv_rev,mul_assoc]


theorem shift_conjugate_apply (p : State n) (c i : Fin n) :
    shiftConjugate p c.val i=p (i+c)-c := by
  have hP (j : Fin n) : (finRotate n^c.val) j=j+c := by
    simpa only [LX.Core.L,Fin.cast_val_eq_self] using AffineLift.rotation_power_apply c.val j
  have hR (j : Fin n) : (finRotate n^c.val)⁻¹ j=j-c := by
    apply (finRotate n^c.val).injective
    change (finRotate n^c.val) ((finRotate n^c.val).symm j)=(finRotate n^c.val) (j-c)
    rw [Equiv.apply_symm_apply,hP,sub_add_cancel]
  simp only [shiftConjugate,Equiv.Perm.mul_apply,hP,hR]


end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

theorem rotation_inversion_change (p : State (k+1)) :
    (inversionNumber (rotateConjugate p) : ℤ)-(inversionNumber p : ℤ)=
      if p 0=0 then 0 else 2*(k+1 : ℤ)-2*(p 0 : ℤ)-2*(p.symm 0 : ℤ) := by
  have hd := congrArg (fun v : ℕ => (v : ℤ)) (domain_rotation_inversions p)
  have hv := congrArg (fun v : ℕ => (v : ℤ)) (value_rotation_inversions (p*finRotate (k+1)))
  push_cast at hd hv
  simp only [← mul_assoc] at hv
  change (inversionNumber (rotateConjugate p) : ℤ)+2*((p*finRotate (k+1))⁻¹ 0 : ℤ)=
    (inversionNumber (p*finRotate (k+1)) : ℤ)+(k : ℤ) at hv
  have hb : ((p*finRotate (k+1))⁻¹ 0 : ℤ)=
      (p.symm 0 : ℤ)-1+(if p.symm 0=0 then (k+1 : ℤ) else 0) := by
    simpa only [mul_inv_rev,Equiv.Perm.mul_apply,Equiv.Perm.inv_def] using inverse_rotate_int (p.symm 0)
  rw [hb] at hv
  by_cases hp : p 0=0
  · have hp' : p.symm 0=0 := by simpa only [hp] using p.symm_apply_apply 0
    simp only [hp',ite_true,Fin.val_zero,Nat.cast_zero] at hv
    simp only [hp,Fin.val_zero,Nat.cast_zero] at hd
    simp only [hp,ite_true]
    linarith only [hd,hv]
  · have hp' : p.symm 0 ≠ 0 := by
      intro h
      apply hp
      have he := congrArg p h
      simpa only [Equiv.apply_symm_apply] using he.symm
    simp only [hp',ite_false] at hv
    simp only [hp,ite_false]
    linarith only [hd,hv]

theorem rotation_energy_minus_inversions (p : State (k+1)) :
    (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement (rotateConjugate p) i|)-
      (inversionNumber (rotateConjugate p) : ℤ)=
    (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ) := by
  have hE := rotation_energy_change p
  have hI := rotation_inversion_change p
  linarith only [hE,hI]



end LX.Core.FiniteCuts

end

section
namespace LX.FiniteJoin
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem shift_depth_deficit (q : State n) (t : ℕ) :
    depthDeficit (shiftConjugate q t)=depthDeficit q := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k =>
    induction t with
    | zero => simp [shiftConjugate,depthDeficit]
    | succ t ih =>
      rw [shift_conjugate_succ]
      exact (rotation_energy_minus_inversions (shiftConjugate q t)).trans ih







end LX.FiniteJoin

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem cyclic_offset_normalized (p : State n) (a i : Fin n) :
    cyclicOffset p a i=permutation p a i-i := by
  unfold cyclicOffset
  change p i-i-(p a-a)=p i+(a-p a)-i
  abel










end LX.AnchoredPhases

end

section
/-! Restrict a permutation and its lift to an invariant union of cycles.
Balance of the retained lift is stated separately from invariance. -/
namespace LX.Core.PrunedLift
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem permutation_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    permutation p S hS i=if i ∈ S then p i else i := rfl

@[simp] theorem permutation_symm_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    (permutation p S hS).symm i=if i ∈ S then p.symm i else i := rfl

end LX.Core.PrunedLift

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
namespace LX.PairCore
open scoped BigOperators
variable {n : ℕ}







@[simp] theorem permutation_apply (q : State n) (i : Fin n) :
    permutation q i=if q (q i)=i then q i else i := by
  simp [permutation,positions]












end LX.PairCore

namespace LX.AnchoredPhases
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases

end

section
namespace LX.CycleGeometry
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem shift_support_and_cycle_count (q : State n) (t : ℕ) :
    (shiftConjugate q t).support.card=q.support.card ∧
      (shiftConjugate q t).cycleFactorsFinset.card=q.cycleFactorsFinset.card := by
  constructor
  · simpa only [shiftConjugate,inv_inv] using
      (Equiv.Perm.card_support_conj (σ := (finRotate n^t)⁻¹) (τ := q))
  · have hh := congrArg Multiset.card (Equiv.Perm.cycleType_conj
      (σ := q) (τ := (finRotate n^t)⁻¹))
    simpa only [shiftConjugate,inv_inv,Equiv.Perm.cycleType,Multiset.card_map,Finset.card_def] using hh

theorem shift_cycle_defect (q : State n) (t : ℕ) :
    cycleDefect (shiftConjugate q t)=cycleDefect q := by
  have hh := LX.FiniteJoin.shift_depth_deficit q t
  obtain ⟨hs,hc⟩ := shift_support_and_cycle_count q t
  unfold cycleDefect
  rw [hs,hc]
  change LX.FiniteJoin.depthDeficit (shiftConjugate q t)-_+_=
    LX.FiniteJoin.depthDeficit q-_+_
  rw [hh]




end LX.CycleGeometry

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem even_unit_two_fixed_offsets_even {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (_root_.LX.AnchoredPhases.displacement p a) : ℤ)+1=(m : ℤ)*(m-1))
    (hfixed : ∀ b : Fin n,GlobalMinimum p b → (fixedPositions (permutation p b)).card=2) :
    ∀ b : Fin n,GlobalMinimum p b → ∀ i : Fin n,(cyclicOffset p b i).val%2=0 := by
  have hunit_at (b : Fin n) (hb : GlobalMinimum p b) :
      (inversions (_root_.LX.AnchoredPhases.displacement p b) : ℤ)+1=(m : ℤ)*(m-1) := by
    have hx := Nat.le_antisymm (global_minimum_exchanges hb a) (global_minimum_exchanges ha b)
    rwa [hx]
  have main : ∀ r : ℕ,∀ b : Fin n,GlobalMinimum p b → ∀ i : Fin n,
      (cyclicOffset p b i).val=r → r%2=0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro b hb i hir
      have hh := (even_unit_reserve_height m hn hb (hunit_at b hb)).1
      have hno := two_fixed_no_offset_one p b (global_minimum_majorized hb)
        (by omega) (hfixed b hb) i
      by_cases hr : r < 2
      · have hz : r=0 := by omega
        simp [hz]
      · obtain ⟨c,hc,hbc⟩ := even_unit_two_fixed_next_phase hn4 m hn hb (hunit_at b hb) (hfixed b hb)
        have hval2 : (2 : Fin n).val=2 := by simp [Nat.mod_eq_of_lt (by omega : 2 < n)]
        have hci : (cyclicOffset p c i).val=r-2 := by
          rw [cyclic_offset_reanchor p b c i,hbc,Fin.coe_sub_iff_le.mpr (show (2 : Fin n) ≤ cyclicOffset p b i by
            change (2 : Fin n).val ≤ (cyclicOffset p b i).val
            rw [hval2,hir]
            omega),hir,hval2]
        have hh' := ih (r-2) (by omega) c hc i hci
        omega
  intro b hb i
  exact main _ b hb i rfl







end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The existence of a one-fixed-point minimal phase is geometric and
independent of any chosen LX upper-bound constant. -/
theorem solution {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (_root_.LX.AnchoredPhases.displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) :
    ∃ b : Fin n,GlobalMinimum p b ∧ (fixedPositions (permutation p b)).card=1 := by
  classical
  by_contra hnone
  have hfixed (b : Fin n) (hb : GlobalMinimum p b) : (fixedPositions (permutation p b)).card=2 := by
    have hx := Nat.le_antisymm (global_minimum_exchanges hb a) (global_minimum_exchanges ha b)
    have hunitb : (inversions (_root_.LX.AnchoredPhases.displacement p b) : ℤ)+1=(m : ℤ)*(m-1) := by rwa [hx]
    have hc := (even_unit_reserve_source m hn hb hunitb).2.2.1
    rcases hc with hc | hc
    · exact False.elim (hnone ⟨b,hb,hc⟩)
    · exact hc
  let q := permutation p a
  let Q := shiftConjugate q a.val
  have hf := hfixed a ha
  have hp := even_unit_two_fixed_offsets_even hn4 m hn ha hunit hfixed a ha
  obtain ⟨hz,_,_,hexcess⟩ := even_unit_reserve_source m hn ha hunit
  rw [hf] at hexcess
  have he (i : Fin n) : Even (q i-i) := by
    have hh : Even (cyclicOffset p a i) := Fin.even_of_val (Nat.even_iff.mpr (hp i))
    rwa [cyclic_offset_normalized] at hh
  have hQeven (i : Fin n) : Even (Q i-i) := by
    have hh := he (i+a)
    have hdiff : Q i-i=q (i+a)-(i+a) := by
      dsimp only [Q]
      rw [shift_conjugate_apply]
      ring
    rwa [hdiff]
  have hQzero : cycleDefect Q=0 := by
    dsimp only [Q]
    rw [LX.CycleGeometry.shift_cycle_defect]
    exact hz
  have hQ0 : Q 0=0 := by
    simp only [Q,q,shift_conjugate_apply,zero_add,permutation_anchor,sub_self]
  obtain ⟨hs,hc⟩ := LX.CycleGeometry.shift_support_and_cycle_count q a.val
  have hfQ : (fixedPositions Q).card ≤ 2 := by
    have h1 := fixed_positions_card q
    have h2 := fixed_positions_card Q
    change (fixedPositions q).card=2 at hf
    rw [hf] at h1
    have hs' : Q.support.card=q.support.card := hs
    omega
  have hnEven : Even n := ⟨m,by omega⟩
  have hpairs := LX.CycleGeometry.two_fixed_no_neighbor_cycles_are_pairs Q hQzero hQ0 hfQ
    (LX.CycleGeometry.even_displacement_no_neighbor_cycle (by omega) hnEven Q hQeven)
  have hsupport : Q.support.card=2*Q.cycleFactorsFinset.card := by
    rw [← cycle_support_card_sum Q]
    calc
      _ = ∑ _g ∈ Q.cycleFactorsFinset,2 := Finset.sum_congr rfl hpairs
      _ = _ := by simp [mul_comm]
  change Q.support.card=q.support.card at hs
  change Q.cycleFactorsFinset.card=q.cycleFactorsFinset.card at hc
  rw [hs,hc] at hsupport
  change q.support.card=2*q.cycleFactorsFinset.card+2 at hexcess
  omega
