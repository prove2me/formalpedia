-- Prove2me | solution 1 for LX.AnchoredPhases.even_unpaid_binary_height_profile
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-03T07:51:29.95694+00:00
-- url     : https://prove2.me/submissions/95e9ee6e-9e42-4de2-859a-2f9b351cb431

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
import Definitions.Def_LX_MinimumHeightMultiplicity
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_even_constant_unpaid_maximum_fiber_three
import Theorems.Thm_LX_AnchoredPhases_even_constant_unpaid_raw_count_pred
import Theorems.Thm_LX_AnchoredPhases_even_minimum_anchor_count_with_fixed
import Theorems.Thm_LX_AnchoredPhases_even_unpaid_rank_at_most_one
import Theorems.Thm_LX_AnchoredPhases_rank_peak_anchor_bounds
import Theorems.Thm_LX_AnchoredPhases_rank_peak_fixed_count
import Theorems.Thm_LX_AnchoredPhases_zero_surplus_anchor

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
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]









theorem permutation_anchor (p : State n) (a : Fin n) : permutation p a a = a := by
  simp [permutation]






















end LX.AnchoredPhases

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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]








theorem zero_surplus_count_le_raw_offsets (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    (Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card ≤
      (rawOffsets p).card := by
  classical
  let Z := Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)
  have hsub : Z.image (fun t => p a-a+t) ⊆ rawOffsets p := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,_⟩ := zero_surplus_anchor p a hmin t (Finset.mem_filter.mp ht).2
    apply Finset.mem_image.mpr
    refine ⟨b,Finset.mem_univ _,?_⟩
    unfold cyclicOffset at hb
    linear_combination hb
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (add_right_injective (p a-a))] at hc
  exact hc

theorem even_raw_offset_count_with_fixed (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hn : n=2*height p a+2) :
    (n : ℤ)+(((fixedPositions (permutation p a)).card : ℤ)-1)*
        (((fixedPositions (permutation p a)).card : ℤ)-2) ≤
      2*((rawOffsets p).card : ℤ) := by
  have hc := even_minimum_anchor_count_with_fixed p a hmin hn
  have hle := zero_surplus_count_le_raw_offsets p a hmin
  omega




end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]





/-- The full critical constant-height even family is paid at constant 3. -/
theorem even_critical_constant_conjecture_word (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  by_contra hunpaid
  have hc := even_constant_unpaid_raw_count_pred p h hall hh hn hunpaid
  obtain ⟨b,hb,_⟩ := even_constant_unpaid_maximum_fiber_three p h hall hh hn hunpaid
  have hlow := even_raw_offset_count_with_fixed p b
    (fun c => by rw [hall b,hall c]) (by rw [hall b]; exact hn)
  rw [hb] at hlow
  norm_num at hlow
  omega



end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Only the two adjacent heights remain; higher phases have exactly one
fixed position, and some higher phase must occur. -/
theorem solution (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    (∀ b,height p b=height p a ∨ height p b=height p a+1) ∧
      (∀ b,height p b=height p a+1 → (fixedPositions (permutation p b)).card=1) ∧
      ∃ b,height p b=height p a+1 := by
  have hR := even_unpaid_rank_at_most_one p a hn hh hmin hunpaid
  have hb := (rank_peak_anchor_bounds p a 1 hmin hR).1
  refine ⟨?_,?_,?_⟩
  · intro b
    have := hb b
    omega
  · intro b hheight
    have hf := rank_peak_fixed_count p a 1 hR b
    have hpos : 0 < (fixedPositions (permutation p b)).card := Finset.card_pos.mpr
      ⟨b,(mem_fixedPositions _ _).mpr (permutation_anchor p b)⟩
    omega
  · by_contra hnot
    have hall (b : Fin n) : height p b=height p a := by
      have := hb b
      have hne : height p b ≠ height p a+1 := fun he => hnot ⟨b,he⟩
      omega
    exact hunpaid (even_critical_constant_conjecture_word p (height p a) hall hh hn)
