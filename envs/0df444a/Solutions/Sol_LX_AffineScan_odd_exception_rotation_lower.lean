-- Prove2me | solution 1 for LX.AffineScan.odd_exception_rotation_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:17:37.749555+00:00
-- url     : https://prove2.me/submissions/e29c95ed-8e48-40e3-826e-72412b55110d

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_ExceptionalPrefixDelay
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FirstLapFormula
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_emitted_depth_rotation_lower
import Theorems.Thm_LX_AffineScan_prefix_minimum_le_iff
import Theorems.Thm_LX_AffineScan_tail_head_depth_lower
import Theorems.Thm_LX_Core_AffineLift_crossing_row_sum

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



/-- Net displacement plus incoming crossings is exactly the outgoing crossing count. -/
theorem displacement_add_depth {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (i : Fin n) :
    d i+(backwardDepth d i : ℤ)=
      ∑ j, ((LX.Core.AffineLift.crossing d i j).toNat : ℤ) := by
  rw [← LX.Core.AffineLift.crossing_row_sum hd i]
  simp only [backwardDepth,Nat.cast_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  omega














end LX.AffineScan

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



@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]















end LX.Core.FiniteCuts

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]
















/-- When j is a new prefix record, the minimum predecessor depth in that
prefix survives into the queue. -/
theorem prefix_record_rotation_lower (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d))
    (j H : ℕ) (hj : 0 < j) (hjn : j < n) (hH : 0 < H)
    (hr : ∀ i : Fin j, atTarget d i.val ≤ atTarget d j)
    (hd : ∀ k < j,H ≤ atDepth d k)
    (w : List Letter) (hw : ∀ i,run w d i=0) :
    (n-1)*H+j-1 ≤ w.count .l := by
  apply emitted_depth_rotation_lower hn d hb hi j H hj hjn hH _ w hw
  have hnot : ¬ ∃ i : Fin j,atTarget d j < atTarget d i.val := by
    rintro ⟨i,h⟩
    have := hr i
    omega
  rw [emittedDepth,ite_eq_right hnot]
  exact (prefix_minimum_le_iff _ _ _).mpr (fun k hk => hd k (by omega))



end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem neg_displacement_le_depth {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (i : Fin n) :
    -d i ≤ (backwardDepth d i : ℤ) := by
  have hh := displacement_add_depth hd i
  have hs : (0 : ℤ) ≤ ∑ j : Fin n,((LX.Core.AffineLift.crossing d i j).toNat : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  omega





 theorem _root_.LX.UploadHelpers.ExceptionalPrefixDelay.lift_labels_injective {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) : Function.Injective (labels d) := by
  have hl (i : Fin n) : labels d i=p.symm i+(c : Fin n) := by
    simpa only [labels] using LX.Core.AffineLift.lift_residue hd i
  intro i j hij
  rw [hl,hl] at hij
  exact p.symm.injective (add_right_cancel hij)













end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The same one-rotation obstruction in the odd exceptional lift. -/
theorem solution (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (oddException (n := n) m))
    (w : List Letter) (hw : ∀ i,run w (oddException (n := n) m) i=0) :
    (n-1)*(m-1)+1 ≤ w.count .l := by
  have hn2 : 2 ≤ n := by omega
  have hcast (k : ℕ) (hk : k < n) : (k : Fin n).val=k := Nat.mod_eq_of_lt hk
  have hhead : m-1 ≤ backwardDepth (oddException (n := n) m) 0 := by
    have hh := tail_head_depth_lower (oddException (n := n) m) (⟨m+2,by omega⟩ : Fin n) (by
      intro i hi
      have hil : i.val < n := i.isLt
      have hip : m+2 ≤ i.val := hi
      simp only [targets,oddException,Fin.val_zero,Nat.cast_zero,ite_true,zero_add]
      rw [ite_eq_right (by omega : i.val ≠ 0),ite_eq_right (by omega : i.val ≠ 1),
        ite_eq_right (by omega : i.val ≠ 2),ite_eq_right (by omega : ¬i.val ≤ m+1)]
      omega)
    simpa only [show n-(m+2)=m-1 by omega] using hh
  have hpref : ∀ k < 2,m-1 ≤ atDepth (oddException (n := n) m) k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k; exact hhead
    · have hk1 : k=1 := by omega
      subst k
      have hh := neg_displacement_le_depth hd (1 : Fin n)
      have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
      simp only [oddException,hv1,ite_eq_right (by decide : ¬1=0),ite_true] at hh
      change m-1 ≤ backwardDepth (oddException (n := n) m) (1 : Fin n)
      omega
  have hr : ∀ i : Fin 2,atTarget (oddException (n := n) m) i.val ≤ atTarget (oddException (n := n) m) 2 := by
    intro i
    have hil := i.isLt
    simp only [atTarget,oddException,hcast i.val (by omega),hcast 2 (by omega)]
    split_ifs <;> omega
  have hh := prefix_record_rotation_lower hn2 (oddException (n := n) m) hd.1
    (_root_.LX.UploadHelpers.ExceptionalPrefixDelay.lift_labels_injective hd) 2 (m-1) (by omega) (by omega) (by omega) hr hpref w hw
  omega
