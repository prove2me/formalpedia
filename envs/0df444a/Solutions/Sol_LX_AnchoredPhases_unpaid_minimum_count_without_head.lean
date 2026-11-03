-- Prove2me | solution 1 for LX.AnchoredPhases.unpaid_minimum_count_without_head
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:54:24.210676+00:00
-- url     : https://prove2.me/submissions/01777c50-7643-4baf-80ab-bc25e35174bb

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
import Definitions.Def_LX_LowOffsetDropBudget
import Definitions.Def_LX_MinimumOffsetCount
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_lower_offset_drop_bound
import Theorems.Thm_LX_AnchoredPhases_minimum_unpaid_positive_backward

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
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem mem_minimum_raw_offsets (p : State n) (h : ℕ) (t : Fin n) :
    t ∈ minimumRawOffsets p h ↔ ∃ b : Fin n,height p b=h ∧ p b-b=t := by
  simp only [minimumRawOffsets,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]






end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem equal_raw_offset_height (p : State n) (a b : Fin n)
    (he : p a-a=p b-b) : height p a=height p b := by
  have hp : permutation p a=permutation p b := by
    apply Equiv.ext
    intro i
    change p i+(a-p a)=p i+(b-p b)
    linear_combination -he
  simp only [height,hp]







end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- If the head is not a minimum phase, the offset count loses another
position. This conclusion holds in both parity cases. -/
theorem solution (p : State n) (a : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e)
    (hhead : height p 0 ≠ height p a) :
    (minimumRawOffsets p (height p a)).card ≤ height p a := by
  classical
  let M := minimumRawOffsets p (height p a)
  have hheadnot : p 0 ∉ M := by
    intro ht
    obtain ⟨b,hb,hraw⟩ := (mem_minimum_raw_offsets p (height p a) (p 0)).mp ht
    have he := equal_raw_offset_height p b 0 (by simpa using hraw)
    exact hhead (he.symm.trans hb)
  change M.card ≤ height p a
  by_cases hz : (0 : Fin n) ∈ M
  · obtain ⟨b,hb,hraw⟩ := (mem_minimum_raw_offsets p (height p a) 0).mp hz
    have hpb : p b=b := sub_eq_zero.mp hraw
    have heq : permutation p b=p := by ext i; simp [permutation,hpb]
    change (descendingPositions (permutation p b)).card=height p a at hb
    rw [heq] at hb
    let D := (descendingPositions p).erase (p.symm 0)
    let V := D.image (fun i => p i-i)
    have hsub : M ⊆ insert 0 V := by
      intro t ht
      by_cases ht0 : t=0
      · simp [ht0]
      obtain ⟨c,hc,hct⟩ := (mem_minimum_raw_offsets p (height p a) t).mp ht
      have hth : t ≠ p 0 := by intro heq; exact hheadnot (heq ▸ ht)
      obtain ⟨i,hi,hpi,hrawi⟩ := minimum_unpaid_positive_backward p a c e he hn hh hmin hc hunpaid
        (by rwa [hct]) (by rwa [hct])
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr
        ⟨(fun hi0 => hpi (by rw [hi0,Equiv.apply_symm_apply])),hi⟩,hrawi.trans hct⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hv : V.card ≤ D.card := Finset.card_image_le
    have hp0 : p 0 ≠ 0 := by intro heq; exact hheadnot (heq.symm ▸ hz)
    have hpre : p.symm 0 ≠ 0 := by
      intro heq
      have he' := congrArg p heq
      simp only [Equiv.apply_symm_apply] at he'
      exact hp0 he'.symm
    have hmem : p.symm 0 ∈ descendingPositions p := by
      rw [mem_descendingPositions,Equiv.apply_symm_apply,Fin.val_zero]
      exact Fin.pos_iff_ne_zero.mpr hpre
    have hd : D.card=height p a-1 := by dsimp only [D]; rw [Finset.card_erase_of_mem hmem,hb]
    omega
  let S := Finset.univ.filter fun b : Fin n => height p b=height p a
  have hS : S.Nonempty := ⟨a,by simp [S]⟩
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image S (fun b => (p b-b).val) hS
  have hbh : height p b=height p a := (Finset.mem_filter.mp hb).2
  let D := lowerOffsetDrops p (p b-b)
  let V := D.image (fun i => p i-i)
  have hsub : M ⊆ insert (p b-b) V := by
    intro t ht
    by_cases htb : t=p b-b
    · simp [htb]
    obtain ⟨c,hc,hct⟩ := (mem_minimum_raw_offsets p (height p a) t).mp ht
    have ht0 : t ≠ 0 := by intro heq; exact hz (heq ▸ ht)
    have hth : t ≠ p 0 := by intro heq; exact hheadnot (heq ▸ ht)
    obtain ⟨i,hi,_,hrawi⟩ := minimum_unpaid_positive_backward p a c e he hn hh hmin hc hunpaid
      (by rwa [hct]) (by rwa [hct])
    have hcle := hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩)
    have hne : (p c-c).val ≠ (p b-b).val := by
      intro heq
      exact htb (hct.symm.trans (Fin.ext heq))
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,by rw [hrawi]; omega⟩,hrawi.trans hct⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hd := lower_offset_drop_bound p b
  have hp0 : p 0 ≠ p b-b := by
    intro heq
    exact hheadnot ((mem_minimum_raw_offsets _ _ _).mpr ⟨b,hbh,heq.symm⟩)
  rw [hbh,ite_eq_right hp0] at hd
  change D.card+1 ≤ height p a at hd
  omega
