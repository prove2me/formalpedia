-- Prove2me | solution 1 for LX.AffineScan.saturated_sweep_rank_le_run
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:45:02.621772+00:00
-- url     : https://prove2.me/submissions/fe8a0d58-39df-4ea9-8688-8351504f1378

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
import Definitions.Def_LX_AffineRankOrder
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyRotationOptimality
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_compare_exchange_eq
import Theorems.Thm_LX_AffineScan_exchange_targets
import Theorems.Thm_LX_AffineScan_rotate_threshold_rank
import Theorems.Thm_LX_AffineScan_threshold_rank_head
import Theorems.Thm_LX_AffineScan_threshold_rank_one

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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
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


































theorem run_append (u v : List Letter) (d : Fin n → ℤ) :
    run (u ++ v) d = run v (run u d) := by
  induction u generalizing d with
  | nil => rfl
  | cons a u ih => exact ih (step a d)



















end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





















theorem compare_head_zero (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (compareHead d) 0 = min (atTarget d 0) (atTarget d 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  simp only [compareHead, atTarget, Nat.cast_zero, Nat.cast_one, zero_add]
  split_ifs with h
  · simp only [exchange, Equiv.swap_apply_left, h01, ite_true, ite_false, sub_zero]
    rw [min_eq_right (by omega)]
    omega
  · exact (min_eq_left (by omega)).symm

theorem compare_head_one (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (compareHead d) 1 = max (atTarget d 0) (atTarget d 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  simp only [compareHead, atTarget, Nat.cast_zero, Nat.cast_one, zero_add]
  split_ifs with h
  · simp only [exchange, Equiv.swap_apply_right, Ne.symm h01, ite_true, ite_false, add_zero]
    rw [max_eq_left (by omega)]
    omega
  · exact (max_eq_right (by omega)).symm


















end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]






omit [NeZero n] in
theorem rank_le_trans {d e f : Fin n → ℤ} (hde : RankLE d e) (hef : RankLE e f) :
    RankLE d f := fun r v => (hde r v).trans (hef r v)

 theorem _root_.LX.UploadHelpers.AffineRankOrder.split_head_sum (hn : 2 ≤ n) (f : Fin n → ℤ) :
    (∑ i : Fin n,f i)=(∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase 1,f i)+f 0+f 1 := by
  have h10 : (1 : Fin n) ≠ 0 := by intro h; have := Fin.one_eq_zero_iff.mp h; omega
  have h0 := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) f (Finset.mem_univ 0)
  have h1 := Finset.sum_erase_add (s := Finset.univ.erase (0 : Fin n)) f
    (Finset.mem_erase.mpr ⟨h10,Finset.mem_univ 1⟩)
  omega







theorem threshold_rank_before_head (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    thresholdRank d ⟨n-1,by omega⟩ (v+n)=_root_.LX.UploadDefinitions.AffineRankOrder.rankTail d v+
      max ((targets d 0-v)/(n : ℤ)) 0+max ((targets d 1-v)/(n : ℤ)) 0 := by
  have he (i : Fin n) :
      (targets d i-(v+n))/(n : ℤ)+1=(targets d i-v)/(n : ℤ) := by
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have ha : targets d i-(v+n)=(targets d i-v)+(-1)*(n : ℤ) := by ring
    rw [ha,Int.add_mul_ediv_right _ _ hnz]
    omega
  unfold thresholdRank
  have hle (i : Fin n) : i ≤ (⟨n-1,by omega⟩ : Fin n) := by change i.val ≤ n-1; omega
  simp_rw [ite_eq_left (hle _),he]
  exact _root_.LX.UploadHelpers.AffineRankOrder.split_head_sum hn _

 theorem _root_.LX.UploadHelpers.AffineRankOrder.compare_rank_tail (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    _root_.LX.UploadDefinitions.AffineRankOrder.rankTail (compareHead d) v=_root_.LX.UploadDefinitions.AffineRankOrder.rankTail d v := by
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 := (Finset.mem_erase.mp hi).1
  have hi0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have ht : targets (compareHead d) i=targets d i := by
    unfold compareHead
    split_ifs
    · rw [exchange_targets hn,Equiv.swap_apply_of_ne_of_ne hi0 hi1]
    · rfl
  rw [ht]

 theorem _root_.LX.UploadHelpers.AffineRankOrder.compare_rank_levels (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    (targets (compareHead d) 0-v)/(n : ℤ)=
        min ((targets d 0-v)/(n : ℤ)) ((targets d 1-v)/(n : ℤ)) ∧
    (targets (compareHead d) 1-v)/(n : ℤ)=
        max ((targets d 0-v)/(n : ℤ)) ((targets d 1-v)/(n : ℤ)) := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have h0 : targets (compareHead d) 0=min (targets d 0) (targets d 1) := by
    simpa only [targets,atTarget,Fin.val_zero,Nat.cast_zero,hv1,Nat.cast_one,zero_add] using compare_head_zero hn d
  have h1 : targets (compareHead d) 1=max (targets d 0) (targets d 1) := by
    simpa only [targets,atTarget,Fin.val_zero,Nat.cast_zero,hv1,Nat.cast_one,zero_add] using compare_head_one hn d
  rw [h0,h1]
  have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  rcases le_total (targets d 0) (targets d 1) with h | h
  · have hq := Int.ediv_le_ediv hnpos (show targets d 0-v ≤ targets d 1-v by omega)
    rw [min_eq_left h,max_eq_right h,min_eq_left hq,max_eq_right hq]
    exact ⟨rfl,rfl⟩
  · have hq := Int.ediv_le_ediv hnpos (show targets d 1-v ≤ targets d 0-v by omega)
    rw [min_eq_right h,max_eq_left h,min_eq_right hq,max_eq_left hq]
    exact ⟨rfl,rfl⟩

/-- Exact local rank update for the actual LX comparator. The cut just
before the head uses the preceding periodic copy, hence threshold v+n. -/
theorem compare_threshold_rank_head (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    thresholdRank (compareHead d) 0 v=
      max (thresholdRank d ⟨n-1,by omega⟩ (v+n)) (thresholdRank d 1 v-1) := by
  rw [threshold_rank_head hn,_root_.LX.UploadHelpers.AffineRankOrder.compare_rank_tail hn,
    (_root_.LX.UploadHelpers.AffineRankOrder.compare_rank_levels hn d v).1,(_root_.LX.UploadHelpers.AffineRankOrder.compare_rank_levels hn d v).2,
    threshold_rank_before_head hn,threshold_rank_one hn]
  omega

theorem exchange_threshold_rank_tail (hn : 2 ≤ n) (d : Fin n → ℤ)
    (r : Fin n) (hr : r ≠ 0) (v : ℤ) :
    thresholdRank (exchange d) r v=thresholdRank d r v := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have h1r : (1 : Fin n) ≤ r := by
    have hne : r.val ≠ 0 := fun h => hr (Fin.ext h)
    change (1 : Fin n).val ≤ r.val
    omega
  have hp (i : Fin n) : Equiv.swap 0 1 i ≤ r ↔ i ≤ r := by
    by_cases hi0 : i=0
    · subst i; simp [h1r]
    · by_cases hi1 : i=1
      · subst i; simp [h1r]
      · rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  unfold thresholdRank
  simp_rw [exchange_targets hn]
  calc
    _ = ∑ i : Fin n,max ((targets d (Equiv.swap 0 1 i)-v)/(n : ℤ)+
        (if Equiv.swap 0 1 i ≤ r then 1 else 0)) 0 := by simp_rw [hp]
    _ = _ := Equiv.sum_comp (Equiv.swap (0 : Fin n) 1)
      (fun i : Fin n => max ((targets d i-v)/(n : ℤ)+(if i ≤ r then 1 else 0)) 0)

theorem compare_threshold_rank_tail (hn : 2 ≤ n) (d : Fin n → ℤ)
    (r : Fin n) (hr : r ≠ 0) (v : ℤ) :
    thresholdRank (compareHead d) r v=thresholdRank d r v := by
  unfold compareHead
  split_ifs
  · exact exchange_threshold_rank_tail hn d r hr v
  · rfl

theorem compare_rank_le_self (hn : 2 ≤ n) (d : Fin n → ℤ) : RankLE (compareHead d) d := by
  intro r v
  by_cases hr : r=0
  · subst r
    rw [compare_threshold_rank_head hn,threshold_rank_before_head hn,
      threshold_rank_one hn,threshold_rank_head hn]
    omega
  · rw [compare_threshold_rank_tail hn d r hr]

theorem compare_rank_mono (hn : 2 ≤ n) {d e : Fin n → ℤ} (hle : RankLE d e) :
    RankLE (compareHead d) (compareHead e) := by
  intro r v
  by_cases hr : r=0
  · subst r
    rw [compare_threshold_rank_head hn,compare_threshold_rank_head hn]
    exact max_le_max (hle _ _) (by have := hle 1 v; omega)
  · rw [compare_threshold_rank_tail hn d r hr,compare_threshold_rank_tail hn e r hr]
    exact hle r v



theorem compare_rank_le_exchange (hn : 2 ≤ n) (d : Fin n → ℤ) :
    RankLE (compareHead d) (exchange d) := by
  rw [← compare_exchange_eq hn d]
  exact compare_rank_le_self hn _








end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem rotate_rank_mono (hn : 2 ≤ n) {d e : Fin n → ℤ} (hle : RankLE d e) :
    RankLE (rotate d) (rotate e) := by
  intro r v
  rw [rotate_threshold_rank hn,rotate_threshold_rank hn]
  exact hle _ _



end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem compare_head_idempotent (hn : 2 ≤ n) (d : Fin n → ℤ) :
    compareHead (compareHead d)=compareHead d := by
  by_cases hd : d 1+1 < d 0
  · have he : compareHead d=exchange d := by simp [compareHead,hd]
    exact (congrArg compareHead he).trans (compare_exchange_eq hn d)
  · have he : compareHead d=d := by simp [compareHead,hd]
    simp only [he]



theorem saturated_sweep_succ (d : Fin n → ℤ) (t : ℕ) :
    saturatedSweep d (t+1)=compareHead (rotate (saturatedSweep d t)) := rfl











end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Greedy comparisons dominate every literal LX schedule with the same
number of left moves, including skipped or repeated exchanges. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter) :
    RankLE (saturatedSweep d (w.count .l)) (run w d) := by
  induction w using List.reverseRecOn with
  | nil => exact compare_rank_le_self hn d
  | append_singleton w a ih =>
    cases a with
    | x =>
      have hh := rank_le_trans (compare_rank_mono hn ih) (compare_rank_le_exchange hn (run w d))
      have he : compareHead (saturatedSweep d (w.count .l))=saturatedSweep d (w.count .l) :=
        compare_head_idempotent hn _
      rw [he] at hh
      simpa [List.count_append,run_append,run,step] using hh
    | l =>
      have hh := rank_le_trans (compare_rank_mono hn (rotate_rank_mono hn ih))
        (compare_rank_le_self hn (rotate (run w d)))
      simpa [List.count_append,run_append,run,step,saturated_sweep_succ] using hh
