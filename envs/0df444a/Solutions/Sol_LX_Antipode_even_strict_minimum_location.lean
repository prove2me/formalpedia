-- Prove2me | solution 1 for LX.Antipode.even_strict_minimum_location
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:13:04.465173+00:00
-- url     : https://prove2.me/submissions/cc8978cf-1699-4de8-ba5e-8b6f3454880b

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
import Definitions.Def_LX_AntipodeCandidates
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_EvenStrictBase
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_Antipode_even_strict_lift_unique
import Theorems.Thm_LX_Antipode_even_strict_phase_ne_boundary

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
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

theorem center_eq_of_translate (m : ℕ) (z v k : ℤ)
    (hz : z=v+(n : ℤ)*k) (hv : -(m : ℤ) ≤ v ∧ v < (n : ℤ)-m) :
    center (n := n) m z=v := by
  have he : z+m=(v+m)+k*(n : ℤ) := by rw [hz]; ring
  unfold center
  rw [he,Int.add_emod]
  simp only [Int.mul_emod_left,add_zero,Int.emod_eq_of_lt (by omega : 0 ≤ v+m)
    (by omega : v+m < (n : ℤ))]
  omega

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]









end LX.Antipode

end

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- In every nonexceptional balanced phase, a smallest token is either
at the initial head or far enough along the circle to pay the target. -/
theorem solution (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    (hlo : ∀ i,1-(m : ℤ) ≤ d i) (hpar : (c.val+m)%2=0) :
    d 0=1-(m : ℤ) ∨ ∃ j : Fin n,m+2 ≤ j.val ∧ d j=1-(m : ℤ) := by
  have he := even_strict_lift_unique m (by omega) hn c hd hlo
  have hcne := even_strict_phase_ne_boundary m hm hn hd hlo
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hn' : (n : ℤ)=2*m := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  by_cases hcm : c.val=m
  · left
    rw [he]
    have h01 : (0 : Fin n) ≠ 1 := by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_zero,hv1] at this; omega
    have h02 : (0 : Fin n) ≠ 2 := by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_zero,hv2] at this; omega
    unfold evenStrictBase perturbedBoard
    rw [Equiv.swap_apply_of_ne_of_ne h01 h02]
    simp only [Fin.val_zero,Nat.cast_zero,sub_zero,hcm]
    apply center_eq_of_translate (m-1) _ _ 1
    · omega
    · constructor <;> omega
  · have hcm2 : c.val ≠ m+2 := by
      intro hh
      apply hcne
      apply Fin.ext
      have hval : (((m+2 : ℕ)) : Fin n).val=m+2 := Nat.mod_eq_of_lt (by omega)
      omega
    let k : ℕ := (c.val+m)/2
    have hk : 2*k=c.val+m := by
      have hh := Nat.mod_add_div (c.val+m) 2
      dsimp only [k]
      omega
    let jv : ℕ := if k < m then k+m else k
    have hjlo : m+2 ≤ jv := by
      have hclt := c.isLt
      dsimp only [jv]
      split_ifs <;> omega
    have hjhi : jv < n := by
      have hclt := c.isLt
      dsimp only [jv]
      split_ifs <;> omega
    have hjtwice : 2*jv=c.val+m ∨ 2*jv=c.val+m+n := by
      dsimp only [jv]
      split_ifs <;> omega
    let j : Fin n := ⟨jv,hjhi⟩
    have hj1 : j ≠ 1 := by intro hh; have := congrArg Fin.val hh; change jv=(1 : Fin n).val at this; omega
    have hj2 : j ≠ 2 := by intro hh; have := congrArg Fin.val hh; change jv=(2 : Fin n).val at this; omega
    refine Or.inr ⟨j,hjlo,?_⟩
    rw [he]
    unfold evenStrictBase perturbedBoard
    rw [Equiv.swap_apply_of_ne_of_ne hj1 hj2]
    have hjval : (j : ℤ)=(jv : ℤ) := rfl
    rw [hjval]
    rcases hjtwice with hh | hh
    · apply center_eq_of_translate (m-1) _ _ 0
      · omega
      · constructor <;> omega
    · apply center_eq_of_translate (m-1) _ _ (-1)
      · omega
      · constructor <;> omega
