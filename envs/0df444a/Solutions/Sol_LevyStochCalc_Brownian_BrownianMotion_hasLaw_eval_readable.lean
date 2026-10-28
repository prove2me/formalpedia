-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:43.196145+00:00
-- url     : https://prove2.me/submissions/0d987608-6956-485e-9242-d8ad745ab09f

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/MathlibBridge.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- The value of a Brownian motion at a nonnegative time `t` has law `gaussianReal 0 t`. -/
theorem solution (W : LevyStochCalc.Brownian.BrownianMotion P) (t : ℝ≥0) :
    HasLaw (W.W (t : ℝ)) (gaussianReal 0 t) P := by
  have hzero : (fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω) =ᵐ[P] W.W (t : ℝ) := by
    filter_upwards [W.initial_zero] with ω hω using by simp [hω]
  rcases eq_or_lt_of_le t.coe_nonneg with h | h
  · have ht0 : t = 0 := NNReal.coe_injective h.symm
    subst ht0
    rw [gaussianReal_zero_var]
    refine HasLaw.congr (X := fun _ : Ω ↦ (0 : ℝ)) ⟨measurable_const.aemeasurable, by simp⟩ ?_
    filter_upwards [W.initial_zero] with ω hω using by simpa using hω
  · have hmap : P.map (fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω) = gaussianReal 0 t := by
      rw [W.increment_gaussian (s := 0) (t := (t : ℝ)) le_rfl h]
      congr 1
      apply NNReal.coe_injective
      change (t : ℝ) - 0 = (t : ℝ)
      rw [sub_zero]
    exact HasLaw.congr (X := fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω)
      ⟨((W.measurable_eval _).sub (W.measurable_eval 0)).aemeasurable, hmap⟩ hzero.symm
