-- Prove2me | solution 1 for LevyStochCalc.BSDEJ.Solves.continuous_driftLeg
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:52:56.250028+00:00
-- url     : https://prove2.me/submissions/4d31906f-de7c-4acc-b86c-bd6bfec8e77a

import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The drift leg of a Picard iterate

For a drift `b : Ω → ℝ → ℝ` of finite energy on the horizon `[0, T]` and vanishing off it, the
drift leg is the primitive `t ↦ ∫_{[0, t]} b ω s ds`, restricted to the sample points on which
`b ω` is integrable over `[0, T]` and set to `0` elsewhere. That restriction is a `P`-conull set,
so the drift leg is a version of the raw primitive, and on it every path is the primitive of a
globally integrable function, hence continuous.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.integrablePaths` — the sample points whose drift path is integrable
  over the horizon.
* `LevyStochCalc.BSDEJ.Solves.driftLeg` — the primitive of the drift, cut to those sample points.

## Main statements

* `driftLeg_ae_eq` — the drift leg is a version of the raw primitive.
* `setIntegral_Icc_eq_intervalIntegral` — the integral over `[0, t]` is the interval integral
  from `0` to `t`, for every real `t`.
* `continuous_driftLeg` — every path of the drift leg is continuous.
* `stronglyAdapted_driftLeg`, `adapted_driftLeg` — the drift leg is adapted to the filtration of
  the drift.
* `adapted_driftLeg_of_rightCont` — the drift leg is adapted to the filtration already when the
  drift is progressive for the right-continuous filtration.
* `measurable_uncurry_driftLeg` — the drift leg is jointly measurable in time and sample point.
* `driftLeg_sub_ae` — the drift leg at the horizon splits at an intermediate time.
* `lintegral_biSup_sq_driftLeg_lt_top` — the drift leg has finite `S²` seminorm.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### The paths on which the drift is integrable -/

/-! ### The drift leg -/



theorem _root_.solution (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0) (ω : Ω) :
    Continuous fun t => driftLeg b T t ω := by
  by_cases hω : ω ∈ integrablePaths b T
  · have hI : IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume := hω
    have hi : Integrable (b ω) volume := by
      have ha := (integrable_indicator_iff measurableSet_Icc).2 hI
      refine ha.congr (Filter.Eventually.of_forall fun s => ?_)
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T <;>
        simp [Set.indicator_apply, hs, hbz ω s]
    have he : (fun t => driftLeg b T t ω) = fun t => ∫ s in (0 : ℝ)..t, b ω s := by
      funext t
      rw [driftLeg_of_mem hω, setIntegral_Icc_eq_intervalIntegral hbz]
    rw [he]
    have hII (a d : ℝ) : IntervalIntegrable (b ω) volume a d := hi.intervalIntegrable
    first | exact intervalIntegral.continuous_primitive hII | exact?
  · have he : (fun t => driftLeg b T t ω) = fun _ => 0 := by
      funext t
      exact driftLeg_of_notMem hω t
    rw [he]
    exact continuous_const
