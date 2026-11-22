-- Prove2me | solution 1 for LevyStochCalc.BSDEJ.Solves.measurable_uncurry_driftLeg
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:52:28.715795+00:00
-- url     : https://prove2.me/submissions/0ac9125d-3770-4c9e-bbba-080ce3b4e076

import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F002

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



theorem _root_.solution (hbm : Measurable (Function.uncurry b)) :
    Measurable (Function.uncurry (driftLeg b T)) := by
  let D : Set ((ℝ × Ω) × ℝ) := {q | 0 ≤ q.2 ∧ q.2 ≤ q.1.1}
  have hD : MeasurableSet D :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)
  have hb : Measurable (fun q : (ℝ × Ω) × ℝ => b q.1.2 q.2) :=
    hbm.comp (measurable_fst.snd.prodMk measurable_snd)
  have hInt : Measurable (fun q : ℝ × Ω => ∫ s in Set.Icc (0 : ℝ) q.1, b q.2 s) := by
    convert ((hb.indicator hD).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable using 1
    funext q
    rw [← integral_indicator measurableSet_Icc]
    congr 1
  have hGood : MeasurableSet (Prod.snd ⁻¹' integrablePaths b T : Set (ℝ × Ω)) :=
    measurable_snd (measurableSet_integrablePaths hbm)
  convert hInt.indicator hGood using 1
  funext q
  by_cases hq : q.2 ∈ integrablePaths b T <;>
    simp [Function.uncurry, driftLeg, Set.indicator_apply, hq]
