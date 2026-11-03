-- Prove2me | solution 1 for LX.CenteredLift.even_reflection_board_sum
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:03:23.083892+00:00
-- url     : https://prove2.me/submissions/30e270e5-a1d9-4615-a834-539c88c8b378

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_CenteredLift_even_reflection_board_formula

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
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u





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

theorem sum_range_add_ediv (m : ℤ) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, (m + i) / n = m := by
  rw [← Int.natCast_pos] at hn
  lift m % n to ℕ using Int.emod_nonneg m (by grind) with t ht
  calc
    _ = ∑ i ∈ Finset.range n, (m / n + if n - t ≤ i then 1 else 0) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Int.add_ediv_of_pos hn]
        grind [Nat.div_eq_zero_iff, Nat.mod_eq_of_lt]
    _ = n * (m / n) + (Finset.Ico (n - t) n).card := by
      simp [Finset.sum_add_distrib, -tsub_le_iff_right, -Nat.sub_le_iff_le_add,
        ← Nat.Ico_zero_eq_range]
    _ = m := by
      have : m % n < n := Int.emod_lt_of_pos _ hn
      grind [Int.mul_ediv_add_emod, Nat.card_Ico]
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
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

 theorem _root_.LX.UploadHelpers.EvenCenteredMass.sum_mod_add (A : ℤ) (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m,(A+i)%(m : ℤ))=∑ i ∈ Finset.range m,(i : ℤ) := by
  have he (i : ℕ) : (A+i)%(m : ℤ)=A+i-(m : ℤ)*((A+i)/(m : ℤ)) := by
    have hh := Int.mul_ediv_add_emod (A+i) (m : ℤ)
    omega
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Int.sum_range_add_ediv A hm,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

 theorem _root_.LX.UploadHelpers.EvenCenteredMass.sum_mod_sub (A : ℤ) (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m,(A-i)%(m : ℤ))=∑ i ∈ Finset.range m,(i : ℤ) := by
  rw [← Finset.sum_range_reflect]
  calc
    _ = ∑ i ∈ Finset.range m,((A-((m-1 : ℕ) : ℤ))+i)%(m : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hil := Finset.mem_range.mp hi
      have he : A-((m-1-i : ℕ) : ℤ)=A-((m-1 : ℕ) : ℤ)+i := by omega
      rw [he]
    _ = _ := _root_.LX.UploadHelpers.EvenCenteredMass.sum_mod_add _ m hm








end LX.CenteredLift

end

namespace LX.CenteredLift
end LX.CenteredLift
open LX
open LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (m : ℕ) (hm : 0 < m) (hn : n=2*m) (C : ℤ) :
    (∑ i : Fin n,reflectionBoard m C i)=(n : ℤ)*((C+m)%2-1) := by
  have hmod : (∑ i : Fin n,(((C+m)/2-(i : ℤ))%(m : ℤ)))=
      2*∑ i ∈ Finset.range m,(i : ℤ) := by
    change (∑ i : Fin n,(fun k : ℕ => ((C+(m : ℤ))/2-(k : ℤ))%(m : ℤ)) i.val)=_
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ((C+(m : ℤ))/2-(k : ℤ))%(m : ℤ)) n,
      show n=m+m by omega,Finset.sum_range_add]
    have htail : (∑ i ∈ Finset.range m,((C+m)/2-((m+i : ℕ) : ℤ))%(m : ℤ))=
        ∑ i ∈ Finset.range m,((C+m)/2-(i : ℤ))%(m : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      have he : (C+m)/2-((m+i : ℕ) : ℤ)=((C+m)/2-(i : ℤ))-(m : ℤ) := by push_cast; ring
      rw [he]
      simp only [Int.sub_emod,Int.emod_self,sub_zero,Int.emod_emod]
    rw [htail,_root_.LX.UploadHelpers.EvenCenteredMass.sum_mod_sub _ m hm]
    ring
  have hid : (∑ i ∈ Finset.range m,(i : ℤ))*2=(m : ℤ)*((m-1 : ℕ) : ℤ) := by
    have hh := congrArg (fun k : ℕ => (k : ℤ)) (Finset.sum_range_id_mul_two m)
    convert hh using 1 <;> simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] <;> rfl
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  rw [hm1] at hid
  simp only [even_reflection_board_formula m hm hn,Finset.sum_sub_distrib,
    Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,hmod]
  have hn' : (n : ℤ)=2*m := by omega
  nlinarith
