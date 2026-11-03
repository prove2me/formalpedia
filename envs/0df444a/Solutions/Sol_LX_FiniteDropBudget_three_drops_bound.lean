-- Prove2me | solution 1 for LX.FiniteDropBudget.three_drops_bound
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:19:16.0002+00:00
-- url     : https://prove2.me/submissions/98354174-c48e-45b2-8ebb-9bf59bced792

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
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteDropBudget
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_FiniteCuts_cycle_descending_count_lt_support
import Theorems.Thm_LX_Core_FiniteCuts_domain_rotation_inversions
import Theorems.Thm_LX_Core_FiniteCuts_finite_depth_rank
import Theorems.Thm_LX_Core_FiniteCuts_inversion_number_inverse

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
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
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










end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}



theorem rotate_castSucc (i : Fin k) : finRotate (k+1) i.castSucc=i.succ :=
  finRotate_of_lt i.isLt



theorem value_rotation_inversions (p : State (k+1)) :
    inversionNumber ((finRotate (k+1))⁻¹*p)+2*(p⁻¹ 0).val=inversionNumber p+k := by
  have h := domain_rotation_inversions p⁻¹
  have he : p⁻¹*finRotate (k+1)=((finRotate (k+1))⁻¹*p)⁻¹ := by simp
  rw [he,inversion_number_inverse,inversion_number_inverse] at h
  exact h



end LX.Core.FiniteCuts

end

section
namespace LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts



theorem forward_rotate_int {k : ℕ} (i : Fin (k+1)) :
    (finRotate (k+1) i : ℤ)=(i : ℤ)+1-
      if i=Fin.last k then (k+1 : ℤ) else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [rotate_castSucc]
    simp

theorem forward_mass_change {k : ℕ} (p : LX.Core.State (k+1)) :
    (∑ i, |_root_.LX.Core.FiniteCuts.displacement (finRotate (k+1)*p) i|)=
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)+2*(p.symm (Fin.last k) : ℤ)-
        2*(descendingPositions p).card := by
  classical
  have hpoint (i : Fin (k+1)) :
      |_root_.LX.Core.FiniteCuts.displacement (finRotate (k+1)*p) i|=|_root_.LX.Core.FiniteCuts.displacement p i|+1-
        2*(if (p i).val < i.val then (1 : ℤ) else 0)+
        (if i=p.symm (Fin.last k) then 2*(i : ℤ)-(k+1 : ℤ) else 0) := by
    have he : p i=Fin.last k ↔ i=p.symm (Fin.last k) :=
      (Equiv.eq_symm_apply p).symm
    simp only [_root_.LX.Core.FiniteCuts.displacement,Equiv.Perm.mul_apply,forward_rotate_int,he]
    have hi := i.isLt
    have hp := (p i).isLt
    by_cases hm : i=p.symm (Fin.last k)
    · have hv := congrArg Fin.val (he.mpr hm)
      simp only [Fin.val_last] at hv
      rw [ite_eq_left hm]
      split_ifs <;> rw [abs_eq_max_neg,abs_eq_max_neg] <;> omega
    · rw [ite_eq_right hm]
      simp only [sub_zero]
      split_ifs <;> rw [abs_eq_max_neg,abs_eq_max_neg] <;> omega
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,← Finset.mul_sum]
  have hc : (∑ i : Fin (k+1),if (p i).val < i.val then (1 : ℤ) else 0)=
      ((descendingPositions p).card : ℤ) := by simp [descendingPositions]
  rw [hc]
  push_cast
  ring












end LX.FiniteDropBudget

end

namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
open LX
open LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts

/-- Rotating the values gives a drop-count bound with the exact number of
backward unit arrows. No shallow or minimum-phase assumption is needed. -/
theorem solution {k : ℕ} (p : LX.Core.State (k+1)) :
    3*((descendingPositions p).card : ℤ) ≤ (k+1 : ℤ)+
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ)+
        (backwardUnits p).card-1 := by
  classical
  let q := finRotate (k+1)*p
  have hi := value_rotation_inversions q
  have he : (finRotate (k+1))⁻¹*q=p := by dsimp [q]; simp
  have hz : q⁻¹ 0=p.symm (Fin.last k) := by
    apply q.injective
    simp [q,Equiv.Perm.mul_apply]
  rw [he,hz] at hi
  have hm := forward_mass_change p
  have hd := finite_depth_descending q
  have hsubset : descendingPositions p ⊆ descendingPositions q ∪ backwardUnits p := by
    intro i hi
    have hpi := (mem_descendingPositions p i).mp hi
    by_cases hu : (p i).val+1=i.val
    · exact Finset.mem_union_right _ (by simp [backwardUnits,hu])
    · apply Finset.mem_union_left
      rw [mem_descendingPositions]
      have hp : (p i).val < k := by have := i.isLt; omega
      have hrot := finRotate_of_lt hp
      change (finRotate (k+1) (p i)).val < i.val
      rw [hrot]
      change (p i).val+1 < i.val
      omega
  have hc := (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hi' : (inversionNumber p : ℤ)+2*(p.symm (Fin.last k) : ℤ)=
      (inversionNumber q : ℤ)+k := by exact_mod_cast hi
  change (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)=_ at hm
  have hc' : ((descendingPositions p).card : ℤ) ≤
      (descendingPositions q).card+(backwardUnits p).card := by exact_mod_cast hc
  linarith
