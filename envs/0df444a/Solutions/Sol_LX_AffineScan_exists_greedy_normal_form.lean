-- Prove2me | solution 1 for LX.AffineScan.exists_greedy_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:08:59.541706+00:00
-- url     : https://prove2.me/submissions/ad27c38b-a674-4fd6-bffd-f8150d8faad5

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
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_ScanTrace_paid_length_le_any_word
import Theorems.Thm_LX_AffineScan_exists_exact_word_board
import Theorems.Thm_LX_AffineScan_exists_scan_trace
import Theorems.Thm_LX_AffineScan_sorting_word_of_zero

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
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
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



theorem ScanTrace.run_zero {d : Fin n → ℤ} {w : List Letter} (ht : ScanTrace d w) :
    ∀ i, run w d i = 0 := by
  induction ht with
  | done hz => exact hz
  | left _ _ _ ih => exact ih
  | swap _ _ ih => exact ih









/-- The unique forward scan acts on the actual permutation in its exact orientation. -/
theorem exists_realized_scan (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : LX.Core.AffineLift.IsLift p.symm c d) :
    ∃ w : List Letter, ScanTrace d w ∧
      p * eval (w ++ List.replicate ((c : Fin n) - (w.count .l : Fin n)).val .l) = 1 := by
  have hlabels (i : Fin n) : labels d i = p i + (c : Fin n) := by
    simpa only [labels, Equiv.symm_symm] using LX.Core.AffineLift.lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hlabels, hlabels] at hij
    exact p.injective (add_right_cancel hij)
  obtain ⟨w, hw⟩ := exists_scan_trace hn d hd.1 hi
  exact ⟨w, hw, sorting_word_of_zero hn p (c : Fin n) d hlabels w hw.run_zero⟩





end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- A genuine normal form for every LX word: a greedy scan of some
balanced exact lift, followed by its paid final rotation, never costs more. -/
theorem solution (hn : 2 ≤ n) (w : List Letter) :
    ∃ d : Fin n → ℤ,∃ g : List Letter,
      IsLift (eval w) (w.count .l : ℤ) d ∧ ScanTrace d g ∧
      eval (n := n) (paidWord (w.count .l : Fin n) g)=eval w ∧
      (paidWord (w.count .l : Fin n) g).length ≤ w.length := by
  obtain ⟨d,hd,hzero⟩ := exists_exact_word_board hn w
  obtain ⟨g,hg,hgword⟩ := exists_realized_scan hn (eval w).symm (w.count .l : ℤ) d
    (by simpa only [Equiv.symm_symm] using hd)
  have hlabels (i : Fin n) : labels d i=(eval w).symm i+(w.count .l : Fin n) := by
    simpa only [labels,Int.cast_natCast] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hlabels,hlabels] at hij
    exact (eval w).symm.injective (add_right_cancel hij)
  refine ⟨d,g,hd,hg,?_,hg.paid_length_le_any_word hn hd.1 hi w hzero⟩
  have he : (eval (n := n) w)⁻¹*eval (paidWord (w.count .l : Fin n) g)=1 := by
    simpa only [paidWord,Int.cast_natCast,Equiv.Perm.inv_def] using hgword
  exact (inv_mul_eq_one.mp he).symm
