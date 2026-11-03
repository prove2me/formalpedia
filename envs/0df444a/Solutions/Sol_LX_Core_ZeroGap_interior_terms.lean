-- Prove2me | solution 1 for LX.Core.ZeroGap.interior_terms
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:35:33.259202+00:00
-- url     : https://prove2.me/submissions/a9885786-a60f-4785-bc49-d1c6a5805fef

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
/-! The inversion terms reversed by a zero-gap endpoint swap each drop from
one to zero. Other endpoint terms are exchanged in pairs. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem negative_quotient_term {z : ℤ} (hz : z < 0) (hn : -z ≤ (n : ℤ)) : (z/(n : ℤ)).natAbs=1 := by
  rw [Int.ediv_eq_neg_one_of_neg_of_le hz hn]
  decide

theorem nonnegative_quotient_term {z : ℤ} (hz : 0 ≤ z) (hn : z < (n : ℤ)) : (z/(n : ℤ)).natAbs=0 := by
  rw [Int.ediv_eq_zero_of_lt hz hn]
  decide







end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (F : Fin n → ℤ) (v j : Fin n)
    (hj0 : 0 < j.val) (hjv : j.val < v.val)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ)) (hF : F j=(j : ℤ)) :
    inversionTerm F 0 j=1 ∧ inversionTerm F j v=1 ∧
      inversionTerm (swapEndpoints F v) 0 j=0 ∧ inversionTerm (swapEndpoints F v) j v=0 := by
  have h0j : (0 : Fin n) < j := hj0
  have hjv' : j < v := hjv
  have hjne0 : j ≠ 0 := ne_of_gt h0j
  have hjnev : j ≠ v := ne_of_lt hjv'
  have hswap : Equiv.swap 0 v j=j := Equiv.swap_apply_of_ne_of_ne hjne0 hjnev
  refine ⟨?_,?_,?_,?_⟩
  · rw [inversionTerm,ite_eq_left h0j,hF]
    exact negative_quotient_term (by omega) (by omega)
  · rw [inversionTerm,ite_eq_left hjv',hF]
    exact negative_quotient_term (by omega) (by omega)
  · simp only [inversionTerm,ite_eq_left h0j,swapEndpoints,hswap,Equiv.swap_apply_left,hF]
    exact nonnegative_quotient_term (by omega) (by omega)
  · simp only [inversionTerm,ite_eq_left hjv',swapEndpoints,hswap,Equiv.swap_apply_right,hF]
    exact nonnegative_quotient_term (by omega) (by omega)
