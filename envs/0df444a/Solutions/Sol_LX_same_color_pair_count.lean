-- Prove2me | solution 1 for LX.same_color_pair_count
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:40:01.599295+00:00
-- url     : https://prove2.me/submissions/848afd4d-5079-4ca1-adce-8647ec1d59a5

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

namespace LX
end LX


namespace LX
end LX
open LX
open scoped BigOperators
variable {n : ℕ}

theorem solution (χ : Fin n → Bool) :
    2*sameColorPairs χ+n=(colorCount χ true)^2+(colorCount χ false)^2 := by
  have hrow (i : Fin n) : (∑ j : Fin n,if χ i=χ j then 1 else 0)=
      if χ i=true then colorCount χ true else colorCount χ false := by
    have hset : (Finset.univ.filter fun j : Fin n => χ i=χ j)=
        (Finset.univ.filter fun j : Fin n => χ j=χ i) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact eq_comm
    rw [Finset.sum_boole,hset]
    change colorCount χ (χ i)=_
    cases hc : χ i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  have hall : (∑ i : Fin n,∑ j : Fin n,if χ i=χ j then 1 else 0)=
      (colorCount χ true)^2+(colorCount χ false)^2 := by
    simp_rw [hrow]
    rw [Finset.sum_ite]
    have hnot : (Finset.univ.filter fun i : Fin n => ¬χ i=true)=
        (Finset.univ.filter fun i : Fin n => χ i=false) := by ext i; cases χ i <;> simp
    simp only [Finset.sum_const,hnot,smul_eq_mul]
    change colorCount χ true*colorCount χ true+colorCount χ false*colorCount χ false=_
    ring
  have hp (i j : Fin n) : (if χ i=χ j then 1 else 0)=
      (if i < j ∧ χ i=χ j then 1 else 0)+
      (if j < i ∧ χ j=χ i then 1 else 0)+(if i=j then 1 else 0 : ℕ) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_lt h]
    · subst j; simp
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_gt h,eq_comm]
  have hflip : (∑ i : Fin n,∑ j : Fin n,if j < i ∧ χ j=χ i then 1 else 0)=sameColorPairs χ :=
    Finset.sum_comm
  have hsum := congrArg (fun f : Fin n → Fin n → ℕ => ∑ i,∑ j,f i j)
    (funext fun i => funext (hp i))
  simp only [Finset.sum_add_distrib] at hsum
  rw [hall,hflip] at hsum
  have hdiag : (∑ i : Fin n,∑ j : Fin n,if i=j then 1 else 0)=n := by simp
  rw [hdiag] at hsum
  change _=sameColorPairs χ+sameColorPairs χ+n at hsum
  omega
