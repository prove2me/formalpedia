-- Prove2me | solution 1 for NarrowDNF.ResidualGram.residual_square_sum
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:54.712324+00:00
-- url     : https://prove2.me/submissions/8604ac80-3e51-4a00-8083-62e06d0e0cca

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ResidualGram

namespace NarrowDNF.ResidualGram
end NarrowDNF.ResidualGram

section


namespace NarrowDNF.ResidualGram
open scoped BigOperators
variable {Ω α : Type*} [Fintype Ω] [DecidableEq α]



private theorem inner_comm (w f g : Ω → ℝ) : inner w f g = inner w g f := by
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem inner_sub_sub (w f g h j : Ω → ℝ) :
    inner w (fun x => f x-g x) (fun x => h x-j x) =
      inner w f h - inner w f j - inner w g h + inner w g j := by
  unfold inner
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

omit [DecidableEq α] in
private theorem weighted_square_sum (w : Ω → ℝ) (A : Finset α) (v : α → Ω → ℝ) :
    (∑ x, w x * (∑ i ∈ A, v i x)^2) = ∑ i ∈ A, ∑ j ∈ A, inner w (v i) (v j) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring



end NarrowDNF.ResidualGram


end

open NarrowDNF
open NarrowDNF.ResidualGram
open scoped BigOperators
variable {Ω α : Type*} [Fintype Ω] [DecidableEq α]
/-- Exact diagonal/offdiagonal expansion when the original components are
pairwise orthogonal and each original component is orthogonal to the other
components' approximations. All remaining offdiagonal terms are products of
the approximations themselves, as used for equal-rank Hatami components. -/
theorem solution (w : Ω → ℝ) (A : Finset α) (f g : α → Ω → ℝ)
    (hff : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → inner w (f i) (f j) = 0)
    (hfg : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → inner w (f i) (g j) = 0) :
    (∑ x, w x * (∑ i ∈ A, (f i x-g i x))^2) =
      (∑ i ∈ A, ∑ x, w x * (f i x-g i x)^2) +
      ∑ i ∈ A, ∑ j ∈ A.erase i, inner w (g i) (g j) := by
  rw [weighted_square_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.add_sum_erase A _ hi]
  congr 1
  · unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
    rw [inner_sub_sub, hff i hi j hjA (Ne.symm hji), hfg i hi j hjA (Ne.symm hji),
      inner_comm w (g i) (f j), hfg j hjA i hi hji]
    ring
