-- Prove2me | solution 1 for LX.AffineScan.ScanTrace.exchange_count
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:45:28.958693+00:00
-- url     : https://prove2.me/submissions/b173b4d5-694f-45d8-8ebc-4bb0d1c6b8a5

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_exchange_labels
import Theorems.Thm_LX_AffineScan_exchange_targets
import Theorems.Thm_LX_AffineScan_rotate_inversions

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
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
/-! Local invariants for the forward scan used to construct LX words.
This module proves progress and energy descent, not the quadratic price. -/
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem rotate_labels (d : Fin n → ℤ) (i : Fin n) :
    labels (rotate d) i = labels d (finRotate n i) - 1 := by
  simp only [labels, rotate, finRotate_apply]
  abel

theorem rotate_injective (d : Fin n → ℤ) (hi : Function.Injective (labels d)) :
    Function.Injective (labels (rotate d)) := by
  intro i j hij
  simp only [rotate_labels, sub_left_inj] at hij
  exact (finRotate n).injective (hi hij)



theorem exchange_injective (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : Function.Injective (labels (exchange d)) := by
  intro i j hij
  simp only [exchange_labels hn] at hij
  exact (Equiv.swap (0 : Fin n) 1).injective (hi hij)

omit [NeZero n] in
theorem rotate_sum (d : Fin n → ℤ) : ∑ i, rotate d i = ∑ i, d i :=
  Equiv.sum_comp (finRotate n) d


theorem exchange_sum (d : Fin n → ℤ) : ∑ i, exchange d i = ∑ i, d i := by
  simp [exchange, Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp]



































end LX.AffineScan

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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





 theorem _root_.LX.UploadHelpers.ScanInversions.swap_inversion_balance (hn : 2 ≤ n) (F : Fin n → ℤ) :
    LX.Core.LiftedModel.inversionCount (fun i => F (Equiv.swap 0 1 i)) +
        ((F 1 - F 0)/(n : ℤ)).natAbs =
      LX.Core.LiftedModel.inversionCount F + ((F 0 - F 1)/(n : ℤ)).natAbs := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap 0 1
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  have hv1 : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hlt01 : (0 : Fin n) < 1 := by change 0 < (1 : Fin n).val; omega
  have hpoint (i j : Fin n) :
      (if τ i < τ j then ((F j-F i)/(n : ℤ)).natAbs else 0) +
        (if i=0 ∧ j=1 then ((F 1-F 0)/(n : ℤ)).natAbs else 0) =
      (if i < j then ((F j-F i)/(n : ℤ)).natAbs else 0) +
        (if i=1 ∧ j=0 then ((F 0-F 1)/(n : ℤ)).natAbs else 0) := by
    by_cases h01p : i=0 ∧ j=1
    · obtain ⟨rfl,rfl⟩ := h01p
      simp [τ, h01, hlt01, not_lt_of_ge (le_of_lt hlt01)]
    by_cases h10p : i=1 ∧ j=0
    · obtain ⟨rfl,rfl⟩ := h10p
      simp [τ, h01, hlt01, not_lt_of_ge (le_of_lt hlt01)]
    have horder : τ i < τ j ↔ i < j := by
      by_cases hi0 : i=0 <;> by_cases hi1 : i=1 <;>
        by_cases hj0 : j=0 <;> by_cases hj1 : j=1
      all_goals simp only [τ, Equiv.swap_apply_def, hi0, hi1, hj0, hj1, ite_true, ite_false]
      all_goals try subst i
      all_goals try subst j
      all_goals simp_all only [Fin.lt_def, Fin.val_zero, hv1, Fin.ext_iff, ite_true, ite_false,
        h01, Ne.symm h01, not_false_eq_true]
      all_goals try omega
      all_goals simp_all
    simp only [horder, h01p, h10p, ite_false, add_zero]
  have hreindex : LX.Core.LiftedModel.inversionCount (fun i => F (τ i)) =
      ∑ i : Fin n, ∑ j : Fin n,
        if τ i < τ j then ((F j-F i)/(n : ℤ)).natAbs else 0 := by
    unfold LX.Core.LiftedModel.inversionCount
    rw [← Equiv.sum_comp τ (fun i => ∑ j : Fin n,
      if i < j then ((F (τ j)-F (τ i))/(n : ℤ)).natAbs else 0)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp τ (fun j =>
      if τ i < j then ((F (τ j)-F (τ (τ i)))/(n : ℤ)).natAbs else 0)]
    simp only [τ, Equiv.swap_apply_self]
  have hsum := congrArg (fun g : Fin n → Fin n → ℕ => ∑ i, ∑ j, g i j)
    (funext fun i => funext (hpoint i))
  simp only [Finset.sum_add_distrib] at hsum
  have hs01 : (∑ i : Fin n, ∑ j : Fin n,
      if i=0 ∧ j=1 then ((F 1-F 0)/(n : ℤ)).natAbs else 0) =
      ((F 1-F 0)/(n : ℤ)).natAbs := by simp [ite_and]
  have hs10 : (∑ i : Fin n, ∑ j : Fin n,
      if i=1 ∧ j=0 then ((F 0-F 1)/(n : ℤ)).natAbs else 0) =
      ((F 0-F 1)/(n : ℤ)).natAbs := by simp [ite_and]
  rw [hs01, hs10] at hsum
  rw [hreindex]
  exact hsum

 theorem _root_.LX.UploadHelpers.ScanInversions.negative_quotient_abs (g : ℤ) (hg : 0 < g) (hdiv : ¬ (n : ℤ) ∣ g) :
    ((-g)/(n : ℤ)).natAbs = (g/(n : ℤ)).natAbs + 1 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hr0 := Int.emod_nonneg g (ne_of_gt hn)
  have hrn := Int.emod_lt_of_pos g hn
  have hrne : g % (n : ℤ) ≠ 0 := by
    intro h
    exact hdiv (Int.dvd_of_emod_eq_zero h)
  have hrpos : 0 < g % (n : ℤ) := by omega
  have hdecomp := Int.ediv_mul_add_emod g (n : ℤ)
  have hquot : (-g)/(n : ℤ) = -(g/(n : ℤ))-1 := by
    apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hn <;> nlinarith
  have hq0 : 0 ≤ g/(n : ℤ) := Int.ediv_nonneg (le_of_lt hg) (le_of_lt hn)
  rw [hquot]
  have habs := Int.natCast_natAbs (-(g/(n : ℤ))-1)
  have habs' := Int.natCast_natAbs (g/(n : ℤ))
  rw [abs_of_nonpos (by omega)] at habs
  rw [abs_of_nonneg hq0] at habs'
  omega



theorem exchange_inversions (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hdesc : d 1+1 < d 0) :
    inversions (exchange d) + 1 = inversions d := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  have hv1 : ((1 : Fin n) : ℤ) = 1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hg : 0 < targets d 0-targets d 1 := by simp only [targets, Fin.val_zero, Nat.cast_zero, zero_add, hv1]; omega
  have hdiv : ¬ (n : ℤ) ∣ targets d 0-targets d 1 := by
    intro h
    have hh := LX.Core.AffineLift.cast_eq_of_modEq (Int.modEq_iff_dvd.mpr h)
    have hcast (i : Fin n) : ((targets d i : ℤ) : Fin n) = labels d i := by
      simp [targets, labels]
    have hl : labels d 1 = labels d 0 := by
      simpa only [hcast] using hh
    exact h01 (hi hl).symm
  have hp := _root_.LX.UploadHelpers.ScanInversions.negative_quotient_abs (targets d 0-targets d 1) hg hdiv
  have hbal := _root_.LX.UploadHelpers.ScanInversions.swap_inversion_balance hn (targets d)
  have he : (fun i => targets d (Equiv.swap 0 1 i)) = targets (exchange d) :=
    funext (fun i => (exchange_targets hn d i).symm)
  rw [he] at hbal
  change inversions (exchange d) + _ = inversions d + _ at hbal
  have hneg : -(targets d 0-targets d 1) = targets d 1-targets d 0 := by ring
  rw [hneg] at hp
  omega



theorem inversions_zero (d : Fin n → ℤ) (hz : ∀ i, d i = 0) : inversions d = 0 := by
  unfold inversions LX.Core.LiftedModel.inversionCount
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hij
  · have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
    have he : ((j : ℤ)-(i : ℤ))/(n : ℤ) = 0 := by
      apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hn <;> omega
    simp only [targets, hz, add_zero, he, Int.natAbs_zero]
  · rfl















end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Exchanges in the actual forward scan are exactly the affine inversion price. -/
theorem solution (hn : 2 ≤ n) {d : Fin n → ℤ} {w : List Letter}
    (ht : ScanTrace d w) (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d)) :
    w.count .x = inversions d := by
  revert hb hi
  induction ht with
  | done hz =>
    intro _ _
    simpa only [List.count_nil] using (inversions_zero _ hz).symm
  | @left d w _ _ ht ih =>
    intro hb hi
    have hb' : ∑ i, rotate d i = 0 := (rotate_sum d).trans hb
    have hh := ih hb' (rotate_injective d hi)
    simpa [rotate_inversions hn d hb hi] using hh
  | @swap d w hdesc ht ih =>
    intro hb hi
    have hb' : ∑ i, exchange d i = 0 := (exchange_sum d).trans hb
    have hh := ih hb' (exchange_injective hn d hi)
    have hc := exchange_inversions hn d hi hdesc
    simp only [List.count_cons_self]
    omega
