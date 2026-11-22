-- Prove2me | solution 1 for LevyStochCalc.BSDEJ.Solves.driftLeg_sub_ae
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:53:13.937971+00:00
-- url     : https://prove2.me/submissions/d728c1d3-0d93-4f71-be4b-c07dd9baff3c

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



theorem _root_.solution (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    driftLeg b T T =ᵐ[P] fun ω => driftLeg b T t ω + ∫ s in Set.Icc t T, b ω s := by
  filter_upwards [ae_mem_integrablePaths hbm hbq] with ω hω
  have hI : IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume := hω
  rw [driftLeg_of_mem hω T, driftLeg_of_mem hω t]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (ht.trans htT), ← intervalIntegral.integral_of_le ht,
    ← intervalIntegral.integral_of_le htT]
  symm
  apply intervalIntegral.integral_add_adjacent_intervals
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact hI.mono_set (fun _ hs => ⟨hs.1.le, hs.2.trans htT⟩)
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le htT]
    exact hI.mono_set (fun _ hs => ⟨ht.trans hs.1.le, hs.2⟩)
