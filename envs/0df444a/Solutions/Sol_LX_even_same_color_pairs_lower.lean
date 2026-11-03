-- Prove2me | solution 1 for LX.even_same_color_pairs_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:43:24.359549+00:00
-- url     : https://prove2.me/submissions/117e544d-3bf6-4334-8658-3a3f0e68467b

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
import Definitions.Def_LX_TwoColorPairs
import Theorems.Thm_LX_same_color_pair_count

namespace LX
end LX

section
namespace LX
open scoped BigOperators
variable {n : ℕ}





theorem color_count_sum (χ : Fin n → Bool) : colorCount χ true+colorCount χ false=n := by
  have hp (i : Fin n) : (if χ i=true then 1 else 0)+(if χ i=false then 1 else 0)=(1 : ℕ) := by
    cases χ i <;> simp
  have hs := congrArg (fun f : Fin n → ℕ => ∑ i,f i) (funext hp)
  convert hs using 1 <;>
    simp only [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_one,colorCount] <;> rfl









end LX

end

namespace LX
end LX
open LX
open scoped BigOperators
variable {n : ℕ}

theorem solution (χ : Fin n → Bool) (m : ℕ) (hn : n=2*m) :
    m*(m-1) ≤ sameColorPairs χ := by
  by_cases hm : m=0
  · subst m; simp
  have hs := color_count_sum χ
  have hp := same_color_pair_count χ
  have hs' : (colorCount χ true : ℤ)+(colorCount χ false : ℤ)=2*m := by omega
  have hp' : 2*(sameColorPairs χ : ℤ)+(n : ℤ)=
      (colorCount χ true : ℤ)^2+(colorCount χ false : ℤ)^2 := by exact_mod_cast hp
  have hn' : (n : ℤ)=2*m := by omega
  have hm' : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  zify
  rw [hm']
  nlinarith [sq_nonneg ((colorCount χ true : ℤ)-m)]
