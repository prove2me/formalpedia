-- Prove2me | solution 1 for LX.AnchoredPhases.even_constant_unpaid_maximum_fiber_three
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:56:32.971536+00:00
-- url     : https://prove2.me/submissions/7b1b0946-e134-4c29-abfa-c516cf8450a0

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
import Theorems.Thm_LX_AnchoredPhases_drops_outside_maximal_offset_head
import Theorems.Thm_LX_AnchoredPhases_even_constant_unpaid_fiber_range
import Theorems.Thm_LX_AnchoredPhases_even_constant_unpaid_offset_backward
import Theorems.Thm_LX_AnchoredPhases_even_constant_unpaid_raw_count
import Theorems.Thm_LX_AnchoredPhases_even_minimum_anchor_count_with_fixed
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

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]





theorem drops_outside_maximal_offset (p : State n) (a : Fin n)
    (hmax : ∀ i,(p i-i).val ≤ (p a-a).val) :
    (descendingPositions p \ fixedPositions (permutation p a)).card ≤ height p a := by
  have hh := drops_outside_maximal_offset_head p a hmax
  omega




end LX.AnchoredPhases

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



theorem even_constant_unpaid_raw_count_height (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    (rawOffsets p).card ≤ h+2 := by
  classical
  by_cases hz : (0 : Fin n) ∈ rawOffsets p
  · obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hz
    have hpa : p a=a := sub_eq_zero.mp ha
    have he : permutation p a=p := by ext i; simp [permutation,hpa]
    have hheight := hall a
    change (descendingPositions (permutation p a)).card=h at hheight
    rw [he] at hheight
    have hc := even_constant_unpaid_raw_count p h hall hh hn hunpaid
    omega
  obtain ⟨a,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => (p i-i).val) ⟨0,Finset.mem_univ _⟩
  let D := descendingPositions p \ fixedPositions (permutation p a)
  let V := D.image (fun i => p i-i)
  have hsub : rawOffsets p ⊆ V ∪ {p a-a,p 0} := by
    intro t ht
    by_cases hex : t ∈ ({p a-a,p 0} : Finset (Fin n))
    · exact Finset.mem_union_right _ hex
    have ht0 : t ≠ 0 := by intro he; subst t; exact hz ht
    have hth : t ≠ p 0 := by intro he; exact hex (by simp [he])
    obtain ⟨i,hi,hraw⟩ := even_constant_unpaid_offset_backward p h hall hh hn hunpaid t ht ht0 hth
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨i,Finset.mem_sdiff.mpr ⟨hi,?_⟩,hraw⟩
    intro hif
    have hf := (mem_fixedPositions _ _).mp hif
    have he : p i-i=p a-a := by
      change p i+(a-p a)=i at hf
      linear_combination hf
    have ht' : t=p a-a := hraw.symm.trans he
    exact hex (by simp [ht'])
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V {p a-a,p 0})
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hd : D.card ≤ h := by
    have hb := drops_outside_maximal_offset p a (fun i => hmax i (Finset.mem_univ _))
    rwa [hall a] at hb
  have he : ({p a-a,p 0} : Finset (Fin n)).card ≤ 2 := by
    have hb := Finset.card_pair_eq_one_or_two (a := p a-a) (b := p 0)
    omega
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

/-- An actual unpaid even constant-height permutation must have maximum
fixed-fiber size exactly three. Fibers of size four are also excluded. -/
theorem solution (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    ∃ b : Fin n,(fixedPositions (permutation p b)).card=3 ∧
      ∀ a,(fixedPositions (permutation p a)).card ≤ 3 := by
  classical
  obtain ⟨b,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun b => (fixedPositions (permutation p b)).card) ⟨0,Finset.mem_univ _⟩
  have hmax' (a : Fin n) := hmax a (Finset.mem_univ _)
  have hlo := (even_constant_unpaid_fiber_range p h hall hh hn b hmax' hunpaid).1
  have hraw := even_constant_unpaid_raw_count_height p h hall hh hn hunpaid
  have hcount := even_raw_offset_count_with_fixed p b
    (fun c => by rw [hall b,hall c]) (by rw [hall b]; exact hn)
  have hn' : (n : ℤ)=2*(h : ℤ)+2 := by exact_mod_cast hn
  have hr : ((rawOffsets p).card : ℤ) ≤ (h : ℤ)+2 := by exact_mod_cast hraw
  have he : (fixedPositions (permutation p b)).card=3 := by
    by_contra hnot
    have hbig : (4 : ℤ) ≤ (fixedPositions (permutation p b)).card := by omega
    have hpos := mul_pos (show (0 : ℤ) < (fixedPositions (permutation p b)).card by omega)
      (show (0 : ℤ) < (fixedPositions (permutation p b)).card-3 by omega)
    nlinarith only [hcount,hn',hr,hpos]
  exact ⟨b,he,fun a => by have := hmax' a; omega⟩
