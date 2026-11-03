-- Prove2me | solution 1 for LX.Core.ZeroGap.endpoint_swap_inversions
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:40:04.206936+00:00
-- url     : https://prove2.me/submissions/5f8fa3a2-afd5-4b14-9032-88f769333029

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
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ZeroGapInversionSum
import Definitions.Def_LX_ZeroGapInversionTerms
import Theorems.Thm_LX_Core_ZeroGap_endpoint_row_terms
import Theorems.Thm_LX_Core_ZeroGap_other_row_terms

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
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
/-! Summing the zero-gap row identities gives the exact inversion decrease. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem sum_two_and_others (f : Fin n → ℕ) (v : Fin n) (hv : v ≠ 0) :
    (∑ i, f i)=f 0+f v+∑ i ∈ otherIndices v, f i := by
  have h0 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : Fin n))
  have hv' := Finset.sum_erase_add (Finset.univ.erase 0) f (by simp [hv] : v ∈ Finset.univ.erase 0)
  unfold otherIndices
  omega

theorem count_positive_below (t : ℕ) (ht0 : 0 < t) (htn : t ≤ n) :
    (∑ i : Fin n, if 0 < i.val ∧ i.val < t then (1 : ℕ) else 0)= (t-1 : ℕ) := by
  rw [Finset.sum_boole]
  have he : (Finset.univ.filter (fun i : Fin n => 0 < i.val ∧ i.val < t))=
      (Finset.univ.filter (fun i : Fin n => i.val < t)).erase 0 := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,ne_eq,Fin.ext_iff,Fin.val_zero]
    omega
  rw [he,Finset.card_erase_of_mem (by simp [ht0]),Fin.card_filter_val_lt,min_eq_right htn]
  simp

theorem count_others_below (v : Fin n) (hv : 0 < v.val) :
    (∑ i ∈ otherIndices v, if 0 < i.val ∧ i.val < v.val then (1 : ℕ) else 0)= (v.val-1 : ℕ) := by
  have he : (∑ i ∈ otherIndices v, if 0 < i.val ∧ i.val < v.val then (1 : ℕ) else 0)=
      ∑ i : Fin n, if 0 < i.val ∧ i.val < v.val then (1 : ℕ) else 0 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hnot
    by_cases hp : 0 < i.val ∧ i.val < v.val
    · have hi0 : i ≠ 0 := by intro h; subst i; simp at hp
      have hiv : i ≠ v := by intro h; subst i; omega
      exact False.elim (hnot (by simp [otherIndices,hi0,hiv]))
    · simp only [ite_eq_right hp]
  rw [he]
  exact count_positive_below v.val hv (Nat.le_of_lt v.isLt)




end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (F : Fin n → ℤ) (v : Fin n) (hv : 0 < v.val)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ))
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → F i=(i : ℤ)) :
    LiftedModel.inversionCount F=LiftedModel.inversionCount (swapEndpoints F v)+(2*v.val-1) := by
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  let row := fun i => ∑ j : Fin n, inversionTerm F i j
  let row' := fun i => ∑ j : Fin n, inversionTerm (swapEndpoints F v) i j
  have hend : row 0+row v=row' 0+row' v+v.val := by
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun j _ => endpoint_row_terms F v j hv hA hB hspan hgap)
    simp only [Finset.sum_add_distrib] at h
    have hc : (∑ j : Fin n, if 0 < j.val ∧ j.val ≤ v.val then (1 : ℕ) else 0)=v.val := by
      have hh := count_positive_below (n := n) (v.val+1) (by omega) v.isLt
      simpa only [Nat.lt_add_one_iff,Nat.add_sub_cancel] using hh
    rw [hc] at h
    exact h
  have hother : ∀ i ∈ otherIndices v, row i=row' i+(if 0 < i.val ∧ i.val < v.val then (1 : ℕ) else 0) := by
    intro i hi
    have hiv : i ≠ v := (Finset.mem_erase.mp hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun j _ => other_row_terms F v i j hi0 hiv hA hB hspan hgap)
    rw [Finset.sum_add_distrib] at h
    by_cases hp : 0 < i.val ∧ i.val < v.val
    · simpa only [ite_eq_left hp,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h
    · simpa only [ite_eq_right hp,Finset.sum_const_zero] using h
  have hs := Finset.sum_congr rfl hother
  rw [Finset.sum_add_distrib,count_others_below v hv] at hs
  have ho := sum_two_and_others row v hv0
  have hn := sum_two_and_others row' v hv0
  change (∑ i, row i)=(∑ i, row' i)+(2*v.val-1)
  calc
    (∑ i, row i) = row 0+row v+∑ i ∈ otherIndices v, row i := ho
    _ = (row 0+row v)+((∑ i ∈ otherIndices v, row' i)+(v.val-1)) := by rw [hs]
    _ = (row' 0+row' v+v.val)+((∑ i ∈ otherIndices v, row' i)+(v.val-1)) := by rw [hend]
    _ = (row' 0+row' v+∑ i ∈ otherIndices v, row' i)+(2*v.val-1) := by omega
    _ = (∑ i, row' i)+(2*v.val-1) := by rw [← hn]
