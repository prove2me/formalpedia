-- Prove2me | solution 1 for NarrowDNF.BourgainSquareFunction.low_degree_le_damped
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:10:52.265046+00:00
-- url     : https://prove2.me/submissions/7bdfb1cf-d929-482c-87d0-9b4dd433bf1c

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier

namespace NarrowDNF.BourgainSquareFunction
end NarrowDNF.BourgainSquareFunction


noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The square function is controlled by any fixed geometric damping of the
full nonnegative component sum. -/
theorem solution (a : (ι → Bool) → ℝ) (k m : ℕ) :
    (∑ s ∈ (Finset.univ.filter fun s => Fourier.degree s ≤ k), a s^2) ≤
      (3 : ℝ)^(m*k) * ∑ s, a s^2 / (3 : ℝ)^(m * Fourier.degree s) := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ s ∈ (Finset.univ.filter fun s => Fourier.degree s ≤ k),
        (3 : ℝ)^(m*k) * (a s^2 / (3 : ℝ)^(m * Fourier.degree s)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hdeg := (Finset.mem_filter.mp hs).2
      have hpow : (3 : ℝ)^(m * Fourier.degree s) ≤ (3 : ℝ)^(m*k) :=
        pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left m hdeg)
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hpow (sq_nonneg (a s))]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => by positivity)
