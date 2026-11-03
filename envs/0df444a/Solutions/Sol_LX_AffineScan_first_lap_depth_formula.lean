-- Prove2me | solution 1 for LX.AffineScan.first_lap_depth_formula
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:12:02.642855+00:00
-- url     : https://prove2.me/submissions/cf574564-efc4-4919-bdb5-6d4043a8451e

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_FirstLapFormula
import Definitions.Def_LX_ForwardCarrier
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_exchange_backward_depth
import Theorems.Thm_LX_AffineScan_exchange_labels
import Theorems.Thm_LX_AffineScan_exists_zero_depth
import Theorems.Thm_LX_AffineScan_sweep_emitted_depth
import Theorems.Thm_LX_AffineScan_sweep_prefix_depth
import Theorems.Thm_LX_AffineScan_sweep_prefix_values
import Theorems.Thm_LX_AffineScan_sweep_step_head_depth
import Theorems.Thm_LX_ForwardCarrier_carrier_le_iff

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




















theorem run_append (u v : List Letter) (d : Fin n → ℤ) :
    run (u ++ v) d = run v (run u d) := by
  induction u generalizing d with
  | nil => rfl
  | cons a u ih => exact ih (step a d)



theorem run_injective (hn : 2 ≤ n) (w : List Letter) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : Function.Injective (labels (run w d)) := by
  induction w generalizing d with
  | nil => exact hi
  | cons a w ih =>
    apply ih
    cases a with
    | l => exact rotate_injective d hi
    | x => exact exchange_injective hn d hi















end LX.AffineScan

end

section
namespace LX.ForwardCarrier











theorem lt_carrier_iff (F : ℕ → ℤ) (k : ℕ) (x : ℤ) :
    x < sweepPrefix F k k ↔ ∃ j ≤ k, x < F j := by
  rw [← not_le, carrier_le_iff]
  push Not
  rfl



end LX.ForwardCarrier

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]













theorem run_sweep_step (d : Fin n → ℤ) : run (sweepStepWord d) d = sweepStep d := by
  unfold sweepStepWord sweepStep compareHead
  split_ifs <;> rfl

theorem run_sweep_word (d : Fin n → ℤ) (k : ℕ) : run (sweepWord d k) d = sweep d k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sweepWord, run_append, ih, run_sweep_step, sweep]


























end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem sweep_injective (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (k : ℕ) :
    Function.Injective (labels (sweep d k)) := by
  rw [← run_sweep_word]
  exact run_injective hn _ d hi













theorem sweep_head_zero (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : backwardDepth (sweep d (n-1)) 0=0 := by
  obtain ⟨i,hi0⟩ := exists_zero_depth d
  have hh := (sweep_prefix_depth hn d hi (n-1) (by omega)).1 i.val (by have := i.isLt; omega)
  simpa [atDepth, hi0] using hh







theorem sweep_add (d : Fin n → ℤ) (a b : ℕ) :
    sweep d (a+b)=sweep (sweep d a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg sweepStep ih










end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem sweep_prefix_head_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (k : ℕ) (hk : k < n) :
    backwardDepth (sweep d k) 0=prefixMinimum (atDepth d) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sweep,sweep_step_head_depth hn _ (sweep_injective hn d hi k),
      ih (by omega),prefixMinimum]
    have hh := (sweep_prefix_depth hn d hi k (by omega)).2 1 (by omega) (by omega)
    change backwardDepth (sweep d k) 1=atDepth d (1+k) at hh
    simpa only [Nat.add_comm 1 k] using congrArg (min (prefixMinimum (atDepth d) k)) hh





theorem comparison_at_prefix (hn : 2 ≤ n) (d : Fin n → ℤ)
    (j : ℕ) (hj : 0 < j) (hjn : j < n) :
    (sweep d (j-1)) 1+1 < (sweep d (j-1)) 0 ↔
      ∃ i : Fin j, atTarget d j < atTarget d i.val := by
  have hv := sweep_prefix_values hn d (j-1) (by omega)
  have ht := hv.2 1 (by omega) (by omega)
  have he : 1+(j-1)=j := by omega
  rw [he] at ht
  have hhead := hv.1
  simp only [atTarget,Nat.cast_zero,Nat.cast_one,zero_add] at ht hhead
  have hh : (sweep d (j-1)) 1+1 < (sweep d (j-1)) 0 ↔
      atTarget d j < ForwardCarrier.sweepPrefix (atTarget d) (j-1) (j-1) := by
    dsimp only [atTarget]
    omega
  rw [hh,ForwardCarrier.lt_carrier_iff]
  constructor
  · rintro ⟨i,hi,hlt⟩
    exact ⟨⟨i,by omega⟩,hlt⟩
  · rintro ⟨i,hi⟩
    exact ⟨i.val,by have := i.isLt; omega,hi⟩

theorem compare_prefix_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (j : ℕ) (hj : 0 < j) (hjn : j < n) :
    backwardDepth (compareHead (sweep d (j-1))) 0=emittedDepth d j := by
  have he := comparison_at_prefix hn d j hj hjn
  have ht := (sweep_prefix_depth hn d hi (j-1) (by omega)).2 1 (by omega) (by omega)
  have hadd : 1+(j-1)=j := by omega
  rw [hadd] at ht
  change backwardDepth (sweep d (j-1)) 1=atDepth d j at ht
  unfold compareHead emittedDepth
  split_ifs with hs hp hp
  · have hh := exchange_backward_depth hn (sweep d (j-1)) hs
    omega
  · exact False.elim (hp (he.mp hs))
  · exact False.elim (hs (he.mpr hp))
  · exact sweep_prefix_head_depth hn d hi (j-1) (by omega)




end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The entire post-lap queue is a closed expression in the original depths
and the original prefix records; no scan state remains on the right. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (i : Fin n) :
    backwardDepth (sweep d (n-1)) i = if i=0 then 0 else emittedDepth d i.val := by
  by_cases hi0 : i=0
  · subst i
    simp only [ite_true]
    exact sweep_head_zero hn d hi
  · rw [ite_eq_right hi0]
    have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
    have hlt := i.isLt
    have hh := sweep_emitted_depth hn (sweep d (i.val-1)) (n-i.val) (by omega) (by omega)
    have ha : i.val-1+(n-i.val)=n-1 := by omega
    have hb : n-(n-i.val)=i.val := by omega
    rw [← sweep_add,ha,hb] at hh
    simp only [atDepth,Fin.cast_val_eq_self] at hh
    rw [hh,compare_prefix_depth hn d hi i.val hip hlt]
