-- Prove2me | solution 1 for LX.AffineScan.exists_scan_trace
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:43:24.379961+00:00
-- url     : https://prove2.me/submissions/5c71b139-9bb9-4782-a1c2-7c9fd8442500

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_exchange_labels
import Theorems.Thm_LX_AffineScan_exists_descent

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
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
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

theorem exchange_energy (hn : 2 ≤ n) (d : Fin n → ℤ) :
    (LX.Core.AffineLift.energy (exchange d) : ℤ) - LX.Core.AffineLift.energy d =
      2 * (d 1 - d 0 + 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by
    intro h
    have h' := Fin.one_eq_zero_iff.mp h.symm
    omega
  have point (i : Fin n) : (exchange d i)^2 = (d (Equiv.swap 0 1 i))^2 +
      (if i = 0 then 2*d 1+1 else 0) + (if i = 1 then -2*d 0+1 else 0) := by
    by_cases hi : i = 0
    · subst i
      simp only [exchange, Equiv.swap_apply_left, h01, ite_true, ite_false, sub_zero, add_zero]
      ring
    · by_cases hj : i = 1
      · subst i
        simp only [exchange, Equiv.swap_apply_right, Ne.symm h01, ite_true, ite_false,
          add_zero]
        ring
      · simp [exchange, Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]
  rw [LX.Core.AffineLift.energy_cast, LX.Core.AffineLift.energy_cast]
  simp_rw [point]
  simp only [Finset.sum_add_distrib]
  rw [Equiv.sum_comp (Equiv.swap (0 : Fin n) 1) (fun i => d i ^ 2)]
  simp
  ring

theorem exchange_energy_lt (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hdesc : d 1 + 1 < d 0) :
    LX.Core.AffineLift.energy (exchange d) < LX.Core.AffineLift.energy d := by
  have h := exchange_energy hn d
  have hh : (LX.Core.AffineLift.energy (exchange d) : ℤ) < LX.Core.AffineLift.energy d := by
    omega
  exact_mod_cast hh













theorem run_sum (w : List Letter) (d : Fin n → ℤ) : ∑ i, run w d i = ∑ i, d i := by
  induction w generalizing d with
  | nil => rfl
  | cons a w ih =>
    rw [run, ih]
    cases a with
    | l => exact rotate_sum d
    | x => exact exchange_sum d

theorem run_injective (hn : 2 ≤ n) (w : List Letter) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : Function.Injective (labels (run w d)) := by
  induction w generalizing d with
  | nil => exact hi
  | cons a w ih =>
    apply ih
    cases a with
    | l => exact rotate_injective d hi
    | x => exact exchange_injective hn d hi







theorem run_left_apply (k : ℕ) (d : Fin n → ℤ) (i : Fin n) :
    run (List.replicate k .l) d i = d (((LX.Core.L n)^k) i) := by
  induction k generalizing d with
  | zero => simp [run]
  | succ k ih =>
    simp only [List.replicate_succ, run, step]
    rw [ih]
    simp only [rotate, LX.Core.L, pow_succ', Equiv.Perm.mul_apply]

theorem run_left_energy (k : ℕ) (d : Fin n → ℤ) :
    LX.Core.AffineLift.energy (run (List.replicate k .l) d) = LX.Core.AffineLift.energy d := by
  simp only [LX.Core.AffineLift.energy, run_left_apply]
  exact Equiv.sum_comp ((LX.Core.L n)^k) (fun i => (d i).natAbs ^ 2)





end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem run_left_zero_iff (k : ℕ) (d : Fin n → ℤ) :
    (∀ i, run (List.replicate k .l) d i = 0) ↔ ∀ i, d i = 0 := by
  simp only [run_left_apply]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := ((LX.Core.L n)^k).surjective i
    exact h j
  · intro h i
    exact h _

theorem ScanTrace.prepend_left (k : ℕ) (d : Fin n → ℤ) (w : List Letter)
    (hz : ¬ ∀ i, d i = 0)
    (hskip : ∀ j < k, run (List.replicate j .l) d 0 ≤ run (List.replicate j .l) d 1 + 1)
    (ht : ScanTrace (run (List.replicate k .l) d) w) :
    ScanTrace d (List.replicate k .l ++ w) := by
  induction k generalizing d with
  | zero => exact ht
  | succ k ih =>
    apply ScanTrace.left hz (hskip 0 (by omega))
    apply ih
    · intro h
      apply hz
      exact (run_left_zero_iff 1 d).mp h
    · intro j hj
      exact hskip (j + 1) (by omega)
    · exact ht









end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Every valid balanced board admits the actual greedy forward scan. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d)) :
    ∃ w : List Letter, ScanTrace d w := by
  generalize he : LX.Core.AffineLift.energy d = E
  induction E using Nat.strong_induction_on generalizing d with
  | h E ih =>
    by_cases hz : ∀ i, d i = 0
    · exact ⟨[], ScanTrace.done hz⟩
    have hex : ∃ k : ℕ, ∃ hk : k < n,
        d (finRotate n ⟨k, hk⟩) + 1 < d ⟨k, hk⟩ := by
      obtain ⟨i, hdesc⟩ := exists_descent hn d hb hi hz
      exact ⟨i.val, i.isLt, hdesc⟩
    let k := Nat.find hex
    obtain ⟨hk, hdesc⟩ := Nat.find_spec hex
    have hcast : (k : Fin n) = ⟨k, hk⟩ := by
      apply Fin.ext
      change k % n = k
      exact Nat.mod_eq_of_lt hk
    let u : List Letter := List.replicate k .l
    let e := run u d
    have he0 : e 0 = d ⟨k, hk⟩ := by
      simp [e, u, run_left_apply, LX.Core.AffineLift.rotation_power_apply, hcast]
    have he1 : e 1 = d (finRotate n ⟨k, hk⟩) := by
      simp only [e, u, run_left_apply, LX.Core.AffineLift.rotation_power_apply, finRotate_apply, hcast]
      congr 1
      abel
    have hdesce : e 1 + 1 < e 0 := by simpa only [he0, he1] using hdesc
    have henergy : LX.Core.AffineLift.energy e = E := (run_left_energy k d).trans he
    have hlt : LX.Core.AffineLift.energy (exchange e) < E := by
      rw [← henergy]
      exact exchange_energy_lt hn e hdesce
    have hb' : ∑ j, exchange e j = 0 := by rw [exchange_sum, run_sum, hb]
    have hi' : Function.Injective (labels (exchange e)) :=
      exchange_injective hn e (run_injective hn u d hi)
    obtain ⟨v, hv⟩ := ih _ hlt (exchange e) hb' hi' rfl
    refine ⟨u ++ .x :: v, ScanTrace.prepend_left k d (.x :: v) hz ?_ (ScanTrace.swap hdesce hv)⟩
    intro j hj
    have hjn : j < n := lt_trans hj hk
    have hnot := Nat.find_min hex hj
    have hh : d ⟨j, hjn⟩ ≤ d (finRotate n ⟨j, hjn⟩) + 1 := by
      by_contra h
      exact hnot ⟨hjn, by omega⟩
    have hjcast : (j : Fin n) = ⟨j, hjn⟩ := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hjn]
    simpa only [run_left_apply, LX.Core.AffineLift.rotation_power_apply, zero_add,
      finRotate_apply, hjcast, add_comm, add_zero] using hh
