-- Prove2me | solution 1 for LX.CenteredLift.odd_reflection_board_sum
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:11:49.296139+00:00
-- url     : https://prove2.me/submissions/202a3300-9942-46cc-b90d-ac8acf8a3ee6

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
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_CenteredLift_odd_reflection_residue_bijective

namespace Int
end Int
namespace LX
end LX
namespace LX.CenteredLift
end LX.CenteredLift
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
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem reflection_board_eq_val (m : ℕ) (C : ℤ) (i : Fin n) :
    reflectionBoard m C i=(reflectionResidue m C i : ℤ)-m := by
  have he : reflectionResidue m C i=(((C-2*(i : ℤ)+m : ℤ)) : Fin n) := by
    simp only [reflectionResidue,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,
      Int.cast_natCast,Fin.cast_val_eq_self]
    ring
  rw [he]
  have hr := Int.emod_nonneg (C-2*(i : ℤ)+m) (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)
  simp only [reflectionBoard,center,Fin.val_intCast,Int.toNat_of_nonneg hr]










end LX.CenteredLift

end

namespace LX.CenteredLift
end LX.CenteredLift
open LX
open LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (m : ℕ) (hn : n=2*m+1) (C : ℤ) :
    ∑ i : Fin n,reflectionBoard m C i=0 := by
  let p : State n := Equiv.ofBijective (reflectionResidue m C) (odd_reflection_residue_bijective m hn C)
  have hs := Equiv.sum_comp p (fun i : Fin n => (i : ℤ))
  change (∑ i : Fin n,(reflectionResidue m C i : ℤ))=∑ i : Fin n,(i : ℤ) at hs
  have ht : (∑ i : Fin n,(i : ℤ))*2=(n : ℤ)*((n-1 : ℕ) : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range]
    have hc := congrArg (fun k : ℕ => (k : ℤ)) (Finset.sum_range_id_mul_two n)
    convert hc using 1 <;> simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] <;> rfl
  have hn1 : ((n-1 : ℕ) : ℤ)=2*m := by omega
  rw [hn1] at ht
  have hval : (∑ i : Fin n,(i : ℤ))=(n : ℤ)*m := by nlinarith
  simp only [reflection_board_eq_val,Finset.sum_sub_distrib,hs,hval,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,sub_self]
