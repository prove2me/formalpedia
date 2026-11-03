-- Prove2me | solution 1 for LX.length_lower_iff_greedy_prices
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:13:23.023241+00:00
-- url     : https://prove2.me/submissions/8c529546-75a6-4a47-bb82-d7f43b1410f8

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
import Theorems.Thm_LX_AffineScan_ScanTrace_exchange_count
import Theorems.Thm_LX_AffineScan_sorting_word_of_zero
import Theorems.Thm_LX_exists_shortest_greedy_word

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













theorem length_le_word {n : ℕ} [NeZero n] (w : List Letter) :
    length (eval (n := n) w) ≤ w.length := by
  exact Nat.sInf_le ⟨w, rfl, rfl⟩















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















end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]























theorem length_eq_counts (w : List Letter) : w.length = w.count .l + w.count .x := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact cost of the actual LX word: inversions plus all rotations, including orientation. -/
theorem ScanTrace.paid_length (hn : 2 ≤ n) {d : Fin n → ℤ} {w : List Letter}
    (ht : ScanTrace d w) (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d))
    (c : Fin n) : (paidWord c w).length = inversions d + paidRotations c w := by
  simp only [paidWord, List.length_append, List.length_replicate, length_eq_counts,
    ht.exchange_count hn hb hi, paidRotations]
  omega





end LX.AffineScan

end

section
namespace LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every balanced lift's greedy price is the length of a literal word
with the specified endpoint, including its final orientation. -/
theorem greedy_lift_price_realized (hn : 2 ≤ n) (p : State n) (c : ℕ)
    (d : Fin n → ℤ) (hd : IsLift p (c : ℤ) d) (g : List Letter) (hg : ScanTrace d g) :
    eval (paidWord (c : Fin n) g)=p ∧
      (paidWord (c : Fin n) g).length=inversions d+paidRotations (c : Fin n) g := by
  have hl (i : Fin n) : labels d i=p.symm i+(c : Fin n) := by
    simpa only [labels,Int.cast_natCast] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.symm.injective (add_right_cancel hij)
  have hs := sorting_word_of_zero hn p.symm (c : Fin n) d hl g hg.run_zero
  have he : p⁻¹*eval (paidWord (c : Fin n) g)=1 := by
    simpa only [paidWord,Equiv.Perm.inv_def] using hs
  exact ⟨(inv_mul_eq_one.mp he).symm,hg.paid_length hn hd.1 hi _⟩





end LX

end

namespace LX
end LX
open LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Exact lower-bound reduction: it is necessary and sufficient to bound
all balanced-lift greedy prices. Restricting to anchor lifts, minimum
energy lifts or minimum height lifts would require another theorem. -/
theorem solution (hn : 2 ≤ n) (p : State n) (B : ℕ) :
    B ≤ length p ↔ ∀ (c : ℕ) (d : Fin n → ℤ) (g : List Letter),
      IsLift p (c : ℤ) d → ScanTrace d g →
        B ≤ inversions d+paidRotations (c : Fin n) g := by
  constructor
  · intro hB c d g hd hg
    obtain ⟨he,hprice⟩ := greedy_lift_price_realized hn p c d hd g hg
    have hlo := length_le_word (n := n) (paidWord (c : Fin n) g)
    rw [he,hprice] at hlo
    exact hB.trans hlo
  · intro h
    obtain ⟨c,d,g,hd,hg,_,hlen⟩ := exists_shortest_greedy_word hn p
    have hb := h c d g hd hg
    have hp := (greedy_lift_price_realized hn p c d hd g hg).2
    omega
