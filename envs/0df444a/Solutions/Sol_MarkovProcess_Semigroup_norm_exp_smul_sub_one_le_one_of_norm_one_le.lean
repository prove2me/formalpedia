-- Prove2me | solution 1 for MarkovProcess.Semigroup.norm_exp_smul_sub_one_le_one_of_norm_one_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:36:12.523928+00:00
-- url     : https://prove2.me/submissions/cf4e4aa2-0d9b-48d7-a794-5abf1efdd9aa

import Definitions.Def_MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Theorems.Thm_MarkovProcess_Semigroup_norm_exp_le_exp_norm_of_norm_one_le

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
theorem solution [CompleteSpace A]
    (hOne : ‖(1 : A)‖ ≤ 1) {c : ℝ} (hc : 0 ≤ c) {Q : A} (hQ : ‖Q‖ ≤ 1) :
    ‖exp (c • (Q - 1))‖ ≤ 1 := by
  have hsplit : c • (Q - 1) = c • Q + (-c) • (1 : A) := by module
  have hcomm : Commute (c • Q) ((-c) • (1 : A)) := by
    exact (Commute.one_right Q).smul_left c |>.smul_right (-c)
  have hexp_scalar : exp ((-c) • (1 : A)) = algebraMap ℝ A (Real.exp (-c)) := by
    have harg : (-c) • (1 : A) = algebraMap ℝ A (-c) := by
      rw [Algebra.smul_def, mul_one]
    rw [harg, Real.exp_eq_exp_ℝ]
    exact (algebraMap_exp_comm (-c)).symm
  calc
    ‖exp (c • (Q - 1))‖ =
        ‖exp (c • Q) * exp ((-c) • (1 : A))‖ := by
      rw [hsplit, exp_add_of_commute hcomm]
    _ ≤ ‖exp (c • Q)‖ * ‖exp ((-c) • (1 : A))‖ := norm_mul_le _ _
    _ ≤
        Real.exp ‖c • Q‖ * ‖exp ((-c) • (1 : A))‖ :=
      mul_le_mul_of_nonneg_right
        (norm_exp_le_exp_norm_of_norm_one_le hOne (c • Q)) (norm_nonneg _)
    _ ≤ Real.exp c * ‖exp ((-c) • (1 : A))‖ := by
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact mul_le_of_le_one_right hc hQ
    _ ≤ Real.exp c * Real.exp (-c) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos c).le
      rw [hexp_scalar, norm_algebraMap, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos (-c)).le hOne
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
