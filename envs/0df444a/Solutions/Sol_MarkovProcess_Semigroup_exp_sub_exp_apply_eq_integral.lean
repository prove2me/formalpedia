-- Prove2me | solution 1 for MarkovProcess.Semigroup.exp_sub_exp_apply_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:16:33.133361+00:00
-- url     : https://prove2.me/submissions/f2ecbbc3-bd16-4795-b646-acb7c6694b48

import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
    (t : ℝ) (x : E) :
    exp (t • B) x - exp (t • A) x =
      ∫ s in 0..t, exp ((t - s) • A) (exp (s • B) ((B - A) x)) := by
  let F : ℝ → E := fun s ↦ exp ((t - s) • A) (exp (s • B) x)
  let F' : ℝ → E :=
    fun s ↦ exp ((t - s) • A) (exp (s • B) ((B - A) x))
  have hderiv : ∀ s : ℝ,
      HasDerivAt F (exp ((t - s) • A) (exp (s • B) ((B - A) x))) s := by
    intro s
    have haffine : HasDerivAt (fun u : ℝ ↦ t - u) (-1) s :=
      by simpa only [Pi.sub_apply, id_eq, zero_sub] using!
        (hasDerivAt_const s t).sub (hasDerivAt_id s)
    have hleft := HasDerivAt.scomp (𝕜 := ℝ) s
      (hasDerivAt_exp_smul_const A (t - s)) haffine
    have hright := HasDerivAt.clm_apply (hasDerivAt_exp_smul_const B s)
      (hasDerivAt_const s x)
    have hproduct := HasDerivAt.clm_apply hleft hright
    have hmove : A (exp (s • B) x) = exp (s • B) (A x) := by
      have hscaled : Commute A (s • B) := by
        calc
          A * (s • B) = s • (A * B) := Algebra.mul_smul_comm s A B
          _ = s • (B * A) := congrArg (fun C : E →L[ℝ] E ↦ s • C) hAB.eq
          _ = (s • B) * A := (Algebra.smul_mul_assoc s B A).symm
      have heq : A * exp (s • B) = exp (s • B) * A := hscaled.exp_right
      exact DFunLike.congr_fun heq x
    refine hproduct.congr_deriv ?_
    simp only [one_smul, neg_smul, ContinuousLinearMap.map_zero, add_zero,
      neg_apply, mul_apply_eq_comp, Function.comp_apply, sub_apply, hmove, map_sub]
    abel
  have hint : IntervalIntegrable F' volume 0 t :=
    (by fun_prop : Continuous F').intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hderiv s) hint
  dsimp only [F] at hFTC
  simpa only [sub_zero, sub_self, zero_smul, exp_zero, one_apply_eq_self]
    using hFTC.symm
