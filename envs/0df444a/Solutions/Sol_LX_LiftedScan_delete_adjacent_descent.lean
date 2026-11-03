-- Prove2me | solution 1 for LX.LiftedScan.delete_adjacent_descent
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:36:19.218208+00:00
-- url     : https://prove2.me/submissions/d00fb5e6-63a7-4bf4-af61-f823471d9ef2

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
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_LiftedModel_before_run_of_absent
import Theorems.Thm_LX_LiftedScan_delete_event_word
import Theorems.Thm_LX_LiftedScan_exact_positions_of_zero

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



























theorem initial_aligned : Aligned (initial (n := n)) := by
  constructor
  · rfl
  · intro i
    simp [initial, PhysicalModel.initial]
    rfl









end LX.Core.LiftedModel

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
namespace LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

























/-- An inversion of periodic token copies must occur as an X event in any
zero-board execution, not only in a reduced trace. -/
theorem event_of_order_change (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hz : ∀ i,AffineScan.run w d i=0) (key : LX.Core.LiftedModel.PairKey n) (hk : key.Valid)
    (hchange : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
      (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift)) :
    key ∈ LX.Core.LiftedModel.events (w.map Letter.toCore) LX.Core.LiftedModel.initial := by
  by_contra hnot
  have hb := LX.Core.LiftedModel.before_run_of_absent hn (w.map Letter.toCore)
    LX.Core.LiftedModel.initial_aligned key hk hnot
  simp only [LX.Core.LiftedModel.PairKey.Before] at hb
  rw [exact_positions_of_zero hn d w hz,exact_positions_of_zero hn d w hz] at hb
  exact hchange hb.symm

theorem delete_crossing_word (hn : 2 ≤ n) (p : State n) (d : Fin n → ℤ) (w : List Letter)
    (hp : p*eval w=1) (hz : ∀ i,AffineScan.run w d i=0)
    (key : LX.Core.LiftedModel.PairKey n) (hk : key.Valid)
    (hchange : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
      (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift)) :
    ∃ v : List Letter,(p*Equiv.swap key.first key.second)*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l :=
  delete_event_word hn p w hp key (event_of_order_change hn d w hz key hk hchange)





end LX.LiftedScan

end

namespace LX.LiftedScan
end LX.LiftedScan
open LX
open LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A descending neighboring pair in the original integer lift must exchange.
The seam case uses a nonzero periodic offset, rather than a linear-order guess. -/
theorem solution (hn : 2 ≤ n) (p : State n) (d : Fin n → ℤ)
    (w : List Letter) (hp : p*eval w=1) (hz : ∀ i,AffineScan.run w d i=0)
    (i : Fin n) (hdesc : d (i+1)+1 < d i) :
    ∃ v : List Letter,(p*Equiv.swap i (i+1))*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l := by
  have hnext : (i+1).val=(i.val+1)%n := by
    rw [Fin.val_add]
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  by_cases hi : i.val+1 < n
  · have hj : (i+1).val=i.val+1 := hnext.trans (Nat.mod_eq_of_lt hi)
    let key : LX.Core.LiftedModel.PairKey n := ⟨i,i+1,0⟩
    have hk : key.Valid := by
      constructor
      · change i.val < (i+1).val
        omega
      · exact dvd_zero _
    have hc : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
        (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift) := by
      dsimp only [key]
      omega
    exact delete_crossing_word hn p d w hp hz key hk hc
  · have hnlast : i.val+1=n := by have := i.isLt; omega
    have hj : i+1=0 := by
      apply Fin.ext
      rw [hnext,hnlast,Nat.mod_self,Fin.val_zero]
    rw [hj] at hdesc
    let key : LX.Core.LiftedModel.PairKey n := ⟨0,i,-(n : ℤ)⟩
    have hk : key.Valid := by
      constructor
      · change (0 : Fin n).val < i.val
        simp only [Fin.val_zero]
        omega
      · exact dvd_neg.mpr (dvd_refl _)
    have hc : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
        (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift) := by
      dsimp only [key]
      simp only [Fin.val_zero,Nat.cast_zero,zero_add]
      omega
    obtain ⟨v,hv,hlen,hrot⟩ := delete_crossing_word hn p d w hp hz key hk hc
    refine ⟨v,?_,hlen,hrot⟩
    simpa only [key,hj,Equiv.swap_comm (0 : Fin n) i] using hv
