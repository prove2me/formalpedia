-- Prove2me | solution 1 for LX.AnchoredPhases.low_offset_count_of_forward_payment
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:21:41.699123+00:00
-- url     : https://prove2.me/submissions/d1f870f0-fa91-48cc-9244-0cc805ead200

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RankPeakCount
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_last_offset_source

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
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
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
namespace LX.PairCore
end LX.PairCore
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
namespace LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



@[simp] theorem mem_fixedPositions (p : State n) (i : Fin n) :
    i ∈ fixedPositions p ↔ p i=i := by simp [fixedPositions]









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

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Count only explicitly excepted minimum gaps and the actual low head.
All other non-backward representatives are paid by the supplied words. -/
theorem solution (p : State n) (h : ℕ) (E : Finset ℕ) {C : ℤ}
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*C)
    (hpay : ∀ b,height p b=h → (b-p b).val ∉ E → p 0 ≠ p b-b →
      (∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val) → ¬(p b).val < b.val →
      ∃ w : List Letter,p*eval w=1 ∧ 4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*C) :
    (minimumHeightOffsets p h).card ≤
      ((descendingPositions p).filter fun i => height p i=h).card+E.card+
        (if height p 0=h then 1 else 0) := by
  classical
  let B := E.image (fun k : ℕ => -(k : Fin n))
  let H : Finset (Fin n) := if height p 0=h then {p 0} else ∅
  let U := B ∪ H
  let V := ((descendingPositions p).filter fun i => height p i=h).image (fun i => p i-i)
  have hsub : minimumHeightOffsets p h ⊆ V ∪ U := by
    intro t ht
    by_cases hbad : t ∈ U
    · exact Finset.mem_union_right _ hbad
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp ht
    have hbh := (Finset.mem_filter.mp hb).2
    obtain ⟨c,hraw,hch,_,hlast⟩ := last_offset_source p b
    have hct : p c-c=t := hraw.trans hbt
    have hcHeight : height p c=h := hch.trans hbh
    by_cases hback : (p c).val < c.val
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr
        ⟨(mem_descendingPositions _ _).mpr hback,hcHeight⟩,hct⟩
    have hgap : (c-p c).val ∉ E := by
      intro he
      apply hbad
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(c-p c).val,he,?_⟩
      simp only [Fin.cast_val_eq_self]
      rw [← hct]
      ring
    have hhead : p 0 ≠ p c-c := by
      intro he
      apply hbad
      have ht0 : t=p 0 := hct.symm.trans he.symm
      have hperm : permutation p 0=permutation p c := by
        apply Equiv.ext
        intro i
        change p i+(0-p 0)=p i+(c-p c)
        linear_combination -he
      have hheight : height p 0=h :=
        (congrArg (fun q : State n => (descendingPositions q).card) hperm).trans hcHeight
      simp [U,H,hheight,ht0]
    exact False.elim (hunpaid (hpay c hcHeight hgap hhead hlast hback))
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V U)
  have hV : V.card ≤ ((descendingPositions p).filter fun i => height p i=h).card := Finset.card_image_le
  have hB : B.card ≤ E.card := Finset.card_image_le
  have hH : H.card=(if height p 0=h then 1 else 0) := by dsimp [H]; split_ifs <;> simp
  have hU : U.card ≤ E.card+(if height p 0=h then 1 else 0) := by
    have hc := Finset.card_union_le B H
    rw [hH] at hc
    change U.card ≤ _ at hc
    omega
  omega
