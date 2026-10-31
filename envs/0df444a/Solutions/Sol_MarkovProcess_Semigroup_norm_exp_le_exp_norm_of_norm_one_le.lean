-- Prove2me | solution 1 for MarkovProcess.Semigroup.norm_exp_le_exp_norm_of_norm_one_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:16:39.804999+00:00
-- url     : https://prove2.me/submissions/5d495843-0799-4d5f-b5ef-e3c78140c1b7

import Definitions.Def_MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Norm bounds for Banach-algebra exponentials

This file records elementary estimates for the exponential in a real Banach algebra.  The
contraction estimate is tailored to exponentials of bounded Yosida-type generators.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess.Semigroup

open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/- `NormedSpace.exp_add_of_commute`'s continuity lemma is now stated for a `ℚ`-normed algebra
(the field argument was dropped); this restricts the existing `NormedAlgebra ℝ A` instance
along `ℚ ↪ ℝ` so it can be found on `A`. -/












end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Norm bounds for Banach-algebra exponentials

This file records elementary estimates for the exponential in a real Banach algebra.  The
contraction estimate is tailored to exponentials of bounded Yosida-type generators.
-/


open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/- `NormedSpace.exp_add_of_commute`'s continuity lemma is now stated for a `ℚ`-normed algebra
(the field argument was dropped); this restricts the existing `NormedAlgebra ℝ A` instance
along `ℚ ↪ ℝ` so it can be found on `A`. -/


namespace MarkovProcess.Semigroup

end MarkovProcess.Semigroup
open MarkovProcess.Semigroup
theorem solution (hOne : ‖(1 : A)‖ ≤ 1) (a : A) :
    ‖exp a‖ ≤ Real.exp ‖a‖ := by
  have hscalar : HasSum (fun n : ℕ ↦ (Nat.factorial n : ℝ)⁻¹ * ‖a‖ ^ n)
      (Real.exp ‖a‖) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa only [smul_eq_mul] using!
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) ‖a‖)
  rw [exp_eq_tsum ℝ]
  calc
    ‖∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ • a ^ n‖ ≤
        ∑' n : ℕ, ‖(Nat.factorial n : ℝ)⁻¹ • a ^ n‖ :=
      norm_tsum_le_tsum_norm (norm_expSeries_summable' a)
    _ ≤ ∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * ‖a‖ ^ n := by
      exact (norm_expSeries_summable' a).tsum_le_tsum (fun n ↦ by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
        cases n with
        | zero => simpa only [pow_zero] using hOne
        | succ n => exact norm_pow_le' a (Nat.succ_pos n))
        hscalar.summable
    _ = Real.exp ‖a‖ := hscalar.tsum_eq
