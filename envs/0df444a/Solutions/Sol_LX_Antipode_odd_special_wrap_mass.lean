-- Prove2me | solution 1 for LX.Antipode.odd_special_wrap_mass
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:14:32.383189+00:00
-- url     : https://prove2.me/submissions/ab49bdac-ef5d-4a6a-b95f-bedf8aa449e7

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
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_OddOuterMass
import Definitions.Def_LX_OddSingleRaise
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_CenteredLift_odd_reflection_board_sum

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
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem center_bounds (m : ℕ) (z : ℤ) :
    -(m : ℤ) ≤ center (n := n) m z ∧ center (n := n) m z < (n : ℤ)-m := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hlo := Int.emod_nonneg (z+m) (ne_of_gt hn)
  have hhi := Int.emod_lt_of_pos (z+m) hn
  unfold center
  omega



theorem center_add (m : ℕ) (z t : ℤ) :
    center (n := n) m (z+t)=center (n := n) m (center (n := n) m z+t) := by
  unfold center
  have h1 : z+t+m=(z+m)+t := by ring
  have h2 : (z+m)%(n : ℤ)-m+t+m=(z+m)%(n : ℤ)+t := by ring
  rw [h1,h2]
  simp only [Int.add_emod,Int.emod_emod]

theorem le_center_of_below_top (m : ℕ) (z : ℤ) (hz : z < (n : ℤ)-m) :
    z ≤ center (n := n) m z := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr (show z+m < (1 : ℤ)*n by omega)
  have hm := mul_nonpos_of_nonpos_of_nonneg (show (z+m)/(n : ℤ) ≤ 0 by omega) (le_of_lt hn)
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  omega

theorem sub_period_le_center_of_at_top (m : ℕ) (z : ℤ) (hz : z ≤ (n : ℤ)-m) :
    z-n ≤ center (n := n) m z := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr (show z+m < (2 : ℤ)*n by omega)
  have hm := mul_le_mul_of_nonneg_right (show (z+m)/(n : ℤ) ≤ 1 by omega) (le_of_lt hn)
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  nlinarith








end LX.CenteredLift

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

theorem add_period_le_center_of_below_bottom (m : ℕ) (z : ℤ) (hz : z < -(m : ℤ)) :
    z+n ≤ center (n := n) m z := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr (show z+m < (0 : ℤ)*n by omega)
  have hm := mul_le_mul_of_nonneg_right (show (z+m)/(n : ℤ) ≤ -1 by omega) (le_of_lt hn)
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  nlinarith

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
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

/-- The special rank at position 2 supplies one whole positive period.
At most one positive mid-rank change can spend that period. -/
theorem solution (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hw : reflectionBoard m ((c : ℤ)+1) (2 : Fin n) ≤ -2) :
    (n : ℤ)-(n : ℤ)*(oddMidTop m c).card ≤ ∑ i,oddBase m hm hn c i := by
  let ρ : State n := oddRank m hm hn
  let e : Fin n → ℤ := reflectionBoard m ((c : ℤ)+1)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have htranslate (i : Fin n) : center (n := n) m (e i+((i : ℤ)-(ρ i : ℤ)))=oddBase m hm hn c i := by
    dsimp only [e,reflectionBoard]
    rw [← center_add]
    unfold oddBase perturbedBoard
    congr 1
    change (c : ℤ)+1-2*(i : ℤ)+((i : ℤ)-(ρ i : ℤ))=(c : ℤ)+1-(ρ i : ℤ)-(i : ℤ)
    ring
  have hp (i : Fin n) : e i+((i : ℤ)-(ρ i : ℤ))+
      (if i=2 then (n : ℤ) else 0)-(if i ∈ oddMidTop m c then (n : ℤ) else 0) ≤ oddBase m hm hn c i := by
    rw [← htranslate]
    have hb : -(m : ℤ) ≤ e i ∧ e i < (n : ℤ)-m := center_bounds m _
    by_cases hi2 : i=2
    · subst i
      have hδ : ((2 : Fin n) : ℤ)-(ρ 2 : ℤ)=1-(m : ℤ) := by
        change ((2 : Fin n).val : ℤ)-(oddRankValue m (2 : Fin n).val : ℤ)=1-(m : ℤ)
        rw [hv2]
        simp only [oddRankValue,ite_true,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        ring
      have hnot : (2 : Fin n) ∉ oddMidTop m c := by
        intro hh
        have ht : 3 ≤ (2 : Fin n).val := (Finset.mem_filter.mp hh).2.1
        rw [hv2] at ht
        omega
      rw [ite_eq_left (show (2 : Fin n)=2 from rfl),ite_eq_right hnot,sub_zero]
      apply add_period_le_center_of_below_bottom
      change e 2 ≤ -2 at hw
      omega
    · rw [ite_eq_right hi2,add_zero]
      by_cases hmid : 3 ≤ i.val ∧ i.val ≤ m+1
      · have hδ : (i : ℤ)-(ρ i : ℤ)=1 := by
          change (i : ℤ)-(oddRankValue m i.val : ℤ)=1
          simp only [oddRankValue,ite_eq_right (by omega : i.val ≠ 2),ite_eq_left hmid]
          omega
        by_cases htop : e i=(m : ℤ)
        · have hmem : i ∈ oddMidTop m c := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmid.1,hmid.2,htop⟩
          rw [ite_eq_left hmem]
          exact sub_period_le_center_of_at_top m _ (by omega)
        · have hnot : i ∉ oddMidTop m c := by
            intro hh
            exact htop (Finset.mem_filter.mp hh).2.2.2
          rw [ite_eq_right hnot,sub_zero]
          exact le_center_of_below_top m _ (by omega)
      · have hδ : (i : ℤ)-(ρ i : ℤ)=0 := by
          change (i : ℤ)-(oddRankValue m i.val : ℤ)=0
          have hine : i.val ≠ 2 := by intro hh; apply hi2; apply Fin.ext; omega
          simp only [oddRankValue,ite_eq_right hine,ite_eq_right hmid,sub_self]
        have hnot : i ∉ oddMidTop m c := by
          intro hh
          have ht := (Finset.mem_filter.mp hh).2
          exact hmid ⟨ht.1,ht.2.1⟩
        rw [ite_eq_right hnot,sub_zero]
        exact le_center_of_below_top m _ (by omega)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
  have hδ : (∑ i : Fin n,((i : ℤ)-(ρ i : ℤ)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp ρ (fun i : Fin n => (i : ℤ)),sub_self]
  have he : (∑ i : Fin n,e i)=0 := odd_reflection_board_sum m hn ((c : ℤ)+1)
  have hloss : (∑ i : Fin n,if i ∈ oddMidTop m c then (n : ℤ) else 0)=(n : ℤ)*(oddMidTop m c).card := by
    simp [mul_comm]
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,he,hδ,hloss,zero_add,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hs
