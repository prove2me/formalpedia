-- Prove2me | solution 1 for LX.AnchoredPhases.next_occupied_phase_with_order
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:37:13.442205+00:00
-- url     : https://prove2.me/submissions/a42fa7f3-edc1-4796-8e81-9fa31eb08f51

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
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_top_phase_inversions
import Theorems.Thm_LX_AnchoredPhases_reanchor_height

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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem fixed_source_displacement (p : State n) (a i : Fin n)
    (hi : i ∈ fixedPositions (permutation p a)) : _root_.LX.AnchoredPhases.displacement p a i= -(height p a : ℤ) := by
  have hh := (mem_fixedPositions _ _).mp hi
  rw [displacement_offset,cyclic_offset_normalized,hh,sub_self]
  simp







end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem offset_zero_iff_source_fixed (p : State n) (a i : Fin n) :
    cyclicOffset p a i=0 ↔ permutation p a i=i := by
  rw [cyclic_offset_normalized,sub_eq_zero]









end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The next occupied raw offset wraps exactly the current fixed positions.
This gives exact height and exchange changes for the original permutation,
including phases which are not globally minimal. -/
theorem solution (p : State n) (a : Fin n) (hh : 0 < height p a) :
    let f := (fixedPositions (permutation p a)).card
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t < n ∧
      (∀ i : Fin n,0 < (cyclicOffset p a i).val → t ≤ (cyclicOffset p a i).val) ∧
      p b-b=p a-a+(t : Fin n) ∧
      (height p b : ℤ)=(height p a : ℤ)+f-t ∧
      (inversions (_root_.LX.AnchoredPhases.displacement p b) : ℤ)-inversions (_root_.LX.AnchoredPhases.displacement p a)=
        (f : ℤ)*((n : ℤ)-2*height p a-f) := by
  classical
  let F := fixedPositions (permutation p a)
  let S := Finset.univ.filter fun i => 0 < (cyclicOffset p a i).val
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hh
    have hmove : permutation p a i ≠ i := by
      have hlt := (mem_descendingPositions _ _).mp hi
      intro he
      rw [he] at hlt
      omega
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    have hne : cyclicOffset p a i ≠ 0 := fun h => hmove ((offset_zero_iff_source_fixed p a i).mp h)
    exact Fin.pos_iff_ne_zero.mpr hne
  obtain ⟨b,hb,hbmin⟩ := Finset.exists_min_image S (fun i => (cyclicOffset p a i).val) hS
  let t := (cyclicOffset p a b).val
  have ht : 0 < t := (Finset.mem_filter.mp hb).2
  have htn : t < n := (cyclicOffset p a b).isLt
  have hbelow (i : Fin n) : (cyclicOffset p a i).val < t ↔ i ∈ F := by
    have hz : (cyclicOffset p a i).val=0 ↔ i ∈ F := by
      have hv : (cyclicOffset p a i).val=0 ↔ cyclicOffset p a i=0 := by
        constructor
        · exact fun h => Fin.ext h
        · exact fun h => congrArg Fin.val h
      rw [hv,offset_zero_iff_source_fixed]
      exact (mem_fixedPositions _ _).symm
    constructor
    · intro hi
      apply hz.mp
      by_contra hnot
      have him : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      have hbi := hbmin i him
      omega
    · intro hi
      rw [hz.mpr hi]
      exact ht
  have hcount : belowCount p a t=F.card := by
    unfold belowCount
    congr 1
    apply Finset.ext
    intro i
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hbelow i
  have hheight := reanchor_height p a b
  change (height p b : ℤ)=(height p a : ℤ)-(t : ℤ)+belowCount p a t at hheight
  rw [hcount] at hheight
  have hFle : F.card ≤ n := (Finset.card_le_univ F).trans_eq (Fintype.card_fin n)
  have hcard : Fᶜ.card=n-F.card := by rw [Finset.card_compl,Fintype.card_fin]
  have heq : _root_.LX.AnchoredPhases.displacement p b=phaseShift (_root_.LX.AnchoredPhases.displacement p a) Fᶜ := by
    funext i
    rw [displacement_offset,cyclic_offset_reanchor p a b i,cyclic_subtraction_value]
    unfold phaseShift
    rw [hcard,Nat.cast_sub hFle,displacement_offset]
    by_cases hi : i ∈ F
    · have hb := (hbelow i).mpr hi
      change (cyclicOffset p a i).val < (cyclicOffset p a b).val at hb
      simp only [hb,ite_true,Finset.mem_compl,hi,not_true_eq_false,ite_false]
      change ((cyclicOffset p a i : ℤ)-(t : ℤ)+(n : ℤ))-(height p b : ℤ)=_
      omega
    · have hb : ¬(cyclicOffset p a i).val < t := fun hb => hi ((hbelow i).mp hb)
      change ¬(cyclicOffset p a i).val < (cyclicOffset p a b).val at hb
      simp only [hb,ite_false,Finset.mem_compl,hi,not_false_eq_true,ite_true]
      change ((cyclicOffset p a i : ℤ)-(t : ℤ)+0)-(height p b : ℤ)=_
      omega
  have htop : ∀ i ∈ Fᶜ,∀ j ∉ Fᶜ,_root_.LX.AnchoredPhases.displacement p a j ≤ _root_.LX.AnchoredPhases.displacement p a i := by
    intro i _ j hj
    have hj' : j ∈ F := by simpa using hj
    rw [fixed_source_displacement p a j hj']
    have hb := (displacement_band p a i).1
    omega
  have hsum : (∑ i ∈ Fᶜ,_root_.LX.AnchoredPhases.displacement p a i)=(F.card : ℤ)*height p a := by
    have hFsum : (∑ i ∈ F,_root_.LX.AnchoredPhases.displacement p a i)= -((F.card : ℤ)*height p a) := by
      calc
        _ = ∑ _i ∈ F,-(height p a : ℤ) := Finset.sum_congr rfl
          (fun i hi => fixed_source_displacement p a i hi)
        _ = _ := by simp
    have hs := Finset.sum_compl_add_sum F (_root_.LX.AnchoredPhases.displacement p a)
    rw [hFsum,displacement_balance] at hs
    omega
  have hI := top_phase_inversions (is_lift p a) Fᶜ (displacement_strict_width p a) htop
  rw [← heq,hcard,Nat.cast_sub hFle,hsum] at hI
  refine ⟨b,t,ht,htn,?_,?_,by change _=_+(F.card : ℤ)-_; omega,?_⟩
  · intro i hi
    exact hbmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  · have ho : cyclicOffset p a b=(t : Fin n) := by simp [t]
    unfold cyclicOffset at ho
    linear_combination ho
  · change _=(F.card : ℤ)*_
    nlinarith
