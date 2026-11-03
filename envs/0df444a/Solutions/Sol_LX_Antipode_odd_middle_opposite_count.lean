-- Prove2me | solution 1 for LX.Antipode.odd_middle_opposite_count
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:08:59.717445+00:00
-- url     : https://prove2.me/submissions/b5b51ef5-194e-4f83-806a-3f2edd66e591

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
import Definitions.Def_LX_AntipodeCandidates
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_OddMiddleInversions
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Antipode
end LX.Antipode
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.LiftedScan
end LX.LiftedScan
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
/-! Reflection in the edge between positions zero and one. It exchanges L/R,
fixes X, and agrees with the word symmetry already used by the lower proof. -/
namespace LX.Core.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



@[simp] theorem reflection_apply (i : Fin n) : reflection i=1-i := rfl

@[simp] theorem reflection_twice (i : Fin n) : reflection (reflection i)=i := by
  simp only [reflection_apply]
  abel

@[simp] theorem reflection_square : (reflection : State n)*reflection=1 := by
  apply Equiv.ext
  intro i
  exact reflection_twice i



end LX.Core.WordReflection

end

section
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]



theorem odd_middle_winding_two (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) : oddBaseWinding m hm hn c 2=0 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hr2 : (oddRank m hm hn (2 : Fin n)).val=m+1 := by
    change oddRankValue m (2 : Fin n).val=m+1
    rw [hv2]
    simp [oddRankValue]
  unfold oddBaseWinding winding
  rw [hr2,hv2]
  have hq : ((c : ℤ)+1-((m+1 : ℕ) : ℤ)-(2 : ℕ)+m)/(n : ℤ)=0 := by
    have hclt := c.isLt
    apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hn' <;> push_cast <;> omega
  rw [hq,neg_zero]

theorem odd_middle_tail_winding (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c j : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    (hj : (c.val+m+2)/2 < j.val) (hjl : j.val ≤ m+1) :
    oddBaseWinding m hm hn c j=1 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hj3 : 3 ≤ j.val := by omega
  have hrj : (oddRank m hm hn j).val=j.val-1 := by
    change oddRankValue m j.val=j.val-1
    simp only [oddRankValue,ite_eq_right (by omega : j.val ≠ 2),
      ite_eq_left (show 3 ≤ j.val ∧ j.val ≤ m+1 from ⟨hj3,hjl⟩)]
  unfold oddBaseWinding winding
  rw [hrj]
  have hq : ((c : ℤ)+1-((j.val-1 : ℕ) : ℤ)-(j : ℤ)+m)/(n : ℤ)= -1 := by
    have hjpred : ((j.val-1 : ℕ) : ℤ)=(j : ℤ)-1 := by omega
    rw [hjpred]
    apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hn' <;> omega
  rw [hq]
  norm_num






end LX.Antipode

end

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]

/-- The opposite-parity rank pairs in the low phase interval provide
the exact extra lower cost needed beyond the uniform reflection bound. -/
theorem solution (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1) :
    (m-c.val+1)/2 ≤ (Finset.univ.filter fun j : Fin n =>
      2 < j.val ∧ j.val ≤ m+1 ∧
      decide (oddBaseWinding m hm hn c 2 % 2=0) ≠
        decide (oddBaseWinding m hm hn c j % 2=0)).card := by
  let a : Fin n := ⟨(c.val+m+2)/2,by omega⟩
  let b : Fin n := ⟨m+1,by omega⟩
  have hsub : Finset.Ioc a b ⊆ (Finset.univ.filter fun j : Fin n =>
      2 < j.val ∧ j.val ≤ m+1 ∧
      decide (oddBaseWinding m hm hn c 2 % 2=0) ≠
        decide (oddBaseWinding m hm hn c j % 2=0)) := by
    intro j hj
    have ht := Finset.mem_Ioc.mp hj
    have hja : (c.val+m+2)/2 < j.val := ht.1
    have hjb : j.val ≤ m+1 := ht.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,by omega,hjb,?_⟩
    rw [odd_middle_winding_two m hm hn c hc,odd_middle_tail_winding m hm hn c j hc hcl hja hjb]
    decide
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Ioc] at hcard
  have hlen : b.val-a.val=(m-c.val+1)/2 := by dsimp only [a,b]; omega
  rwa [hlen] at hcard
