-- Prove2me | solution 1 for MarkovProcess.Semigroup.norm_exp_sub_exp_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:36:13.275762+00:00
-- url     : https://prove2.me/submissions/0d3c0771-1c7a-429b-8348-14d03d8d789f

import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_MarkovProcess_Semigroup_exp_sub_exp_apply_eq_integral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Duhamel estimates for bounded generators

This file gives the variation identity and contraction bounds needed to compare
exponentials of commuting bounded generators.  The identity is oriented as
`exp (t B) - exp (t A)`, so its integrand acts on `(B - A) x` and the resulting
estimate is immediately applicable to Yosida approximants.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NormedSpace Set

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/- Head-class caches: the repeated closed instance searches in this file are all
rooted at the operator type `E →L[ℝ] E`; resolving each once here keeps the
normed-hierarchy walk on `E` from being replayed at every `•` and `exp`. -/




/- `NormedSpace.exp`'s continuity lemma is now stated for a `ℚ`-normed algebra (the field
argument was dropped); this restricts the existing `NormedAlgebra ℝ (E →L[ℝ] E)` instance
along `ℚ ↪ ℝ` so `exp_continuous`/`fun_prop` can find it on `E →L[ℝ] E`. -/








end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Duhamel estimates for bounded generators

This file gives the variation identity and contraction bounds needed to compare
exponentials of commuting bounded generators.  The identity is oriented as
`exp (t B) - exp (t A)`, so its integrand acts on `(B - A) x` and the resulting
estimate is immediately applicable to Yosida approximants.
-/

open MeasureTheory NormedSpace Set


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/- Head-class caches: the repeated closed instance searches in this file are all
rooted at the operator type `E →L[ℝ] E`; resolving each once here keeps the
normed-hierarchy walk on `E` from being replayed at every `•` and `exp`. -/




/- `NormedSpace.exp`'s continuity lemma is now stated for a `ℚ`-normed algebra (the field
argument was dropped); this restricts the existing `NormedAlgebra ℝ (E →L[ℝ] E)` instance
along `ℚ ↪ ℝ` so `exp_continuous`/`fun_prop` can find it on `E →L[ℝ] E`. -/




namespace MarkovProcess.Semigroup

end MarkovProcess.Semigroup
open MarkovProcess.Semigroup
theorem solution (A B : E →L[ℝ] E) (hAB : Commute A B)
    {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • A)‖ ≤ 1)
    (hB : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • B)‖ ≤ 1) (x : E) :
    ‖exp (t • B) x - exp (t • A) x‖ ≤ t * ‖(B - A) x‖ := by
  rw [exp_sub_exp_apply_eq_integral A B hAB t x]
  calc
    ‖∫ s in 0..t, exp ((t - s) • A) (exp (s • B) ((B - A) x))‖
        ≤ ‖(B - A) x‖ * |t - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
      rw [uIoc_of_le ht] at hs
      have hsIcc : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
      have hts : t - s ∈ Icc (0 : ℝ) t :=
        ⟨sub_nonneg.mpr hs.2, sub_le_self t hs.1.le⟩
      calc
        ‖exp ((t - s) • A) (exp (s • B) ((B - A) x))‖
            ≤ ‖exp ((t - s) • A)‖ * ‖exp (s • B) ((B - A) x)‖ :=
          (exp ((t - s) • A)).le_opNorm _
        _ ≤ 1 * ‖exp (s • B) ((B - A) x)‖ :=
          mul_le_mul_of_nonneg_right (hA (t - s) hts) (norm_nonneg _)
        _ = ‖exp (s • B) ((B - A) x)‖ := one_mul _
        _ ≤ ‖exp (s • B)‖ * ‖(B - A) x‖ :=
          (exp (s • B)).le_opNorm _
        _ ≤ 1 * ‖(B - A) x‖ :=
          mul_le_mul_of_nonneg_right (hB s hsIcc) (norm_nonneg _)
        _ = ‖(B - A) x‖ := one_mul _
    _ = t * ‖(B - A) x‖ := by rw [sub_zero, abs_of_nonneg ht, mul_comm]
