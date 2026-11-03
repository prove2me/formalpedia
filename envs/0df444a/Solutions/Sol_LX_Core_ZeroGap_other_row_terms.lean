-- Prove2me | solution 1 for LX.Core.ZeroGap.other_row_terms
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:36:54.464195+00:00
-- url     : https://prove2.me/submissions/482ab25e-60bf-48b0-8e0e-65798aba1fc9

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
import Definitions.Def_LX_ZeroGapInversionTerms
import Theorems.Thm_LX_Core_ZeroGap_interior_terms

namespace Int
end Int
namespace LX
end LX
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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (F : Fin n → ℤ) (v i j : Fin n)
    (hi0 : i ≠ 0) (hiv : i ≠ v)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ))
    (hgap : ∀ k : Fin n, 0 < k.val → k.val < v.val → F k=(k : ℤ)) :
    inversionTerm F i j=inversionTerm (swapEndpoints F v) i j+
      if 0 < i.val ∧ i.val < v.val then (if j=v then 1 else 0) else 0 := by
  have hipos : 0 < i.val := by have h : i.val ≠ 0 := fun h => hi0 (Fin.ext h); omega
  have hiswap : Equiv.swap 0 v i=i := Equiv.swap_apply_of_ne_of_ne hi0 hiv
  by_cases hj0 : j=0
  · subst j
    have hi : ¬i < (0 : Fin n) := by change ¬i.val < 0; omega
    by_cases hc : 0 < i.val ∧ i.val < v.val
    · have hv0 : (0 : Fin n) ≠ v := by intro he; have hz := congrArg Fin.val he; simp at hz; omega
      simp only [inversionTerm,ite_eq_right hi,ite_eq_left hc,ite_eq_right hv0,Nat.add_zero]
    · simp only [inversionTerm,ite_eq_right hi,ite_eq_right hc,Nat.add_zero]
  · by_cases hjv : j=v
    · subst j
      by_cases hlt : i.val < v.val
      · obtain ⟨_,h1,_,h2⟩ := interior_terms F v i hipos hlt hA hB hspan (hgap i hipos hlt)
        simp [h1,h2,hipos,hlt]
      · have hnot : ¬i < v := hlt
        simp [inversionTerm,hnot,hlt]
    · have hjswap : Equiv.swap 0 v j=j := Equiv.swap_apply_of_ne_of_ne hj0 hjv
      simp only [inversionTerm,swapEndpoints,hiswap,hjswap,ite_eq_right hjv]
      split_ifs <;> omega
