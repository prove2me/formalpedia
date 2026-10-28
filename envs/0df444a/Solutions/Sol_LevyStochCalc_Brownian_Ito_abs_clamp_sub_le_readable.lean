-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.abs_clamp_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:20.761293+00:00
-- url     : https://prove2.me/submissions/7d3d803f-e032-4e0e-9899-1574da42ce62

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- Clamping to `[-C, C]` moves a value no further from any target already in `[-C, C]`. -/
theorem solution {C x y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C) :
    |max (-C) (min C x) - y| ≤ |x - y| := by
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  rcases le_or_gt x (-C) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ C), max_eq_left hx,
      abs_of_nonpos (by linarith : -C - y ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · rcases le_or_gt x C with hx' | hx'
    · rw [min_eq_right hx', max_eq_right (by linarith : -C ≤ x)]
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -C ≤ C),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ C - y),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
      linarith
