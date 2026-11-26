-- Prove2me | solution 1 for Kyprianou.Ch04.strictMaskRightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:48:38.947996+00:00
-- url     : https://prove2.me/submissions/91f602db-f401-4eff-b59b-d3d933f387e6

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Strict clipping preserves right continuity on nonnegative time. -/
theorem solution (g : ℝ → ℝ) (tau : WithTop NNReal)
    (hr : ∀ r : ℝ, 0 ≤ r → ContinuousWithinAt g (Ici r) r) :
    ∀ r : ℝ, 0 ≤ r → ContinuousWithinAt
      (fun v => if (v.toNNReal : WithTop NNReal) < tau then g v else 0) (Ici r) r := by
  let k := fun v : ℝ => if (v.toNNReal : WithTop NNReal) < tau then g v else 0
  intro r hr0
  change ContinuousWithinAt k (Ici r) r
  by_cases hb : (r.toNNReal : WithTop NNReal) < tau
  · have hev : ∀ᶠ v in nhdsWithin r (Ici r), (v.toNNReal : WithTop NNReal) < tau :=
      by
        generalize he : tau = a at *
        induction a using WithTop.recTopCoe with
        | top => exact Eventually.of_forall fun v => WithTop.coe_lt_top _
        | coe a =>
          have hlt : r.toNNReal < a := WithTop.coe_lt_coe.mp hb
          have hh : ∀ᶠ v in 𝓝 r, v.toNNReal < a :=
            continuous_real_toNNReal.continuousAt.eventually (Iio_mem_nhds hlt)
          exact (hh.filter_mono nhdsWithin_le_nhds).mono fun v hv => WithTop.coe_lt_coe.mpr hv
    have hEq : (fun v => k v) =ᶠ[nhdsWithin r (Ici r)] fun v => g v :=
      hev.mono fun v hv => if_pos hv
    exact (hr r hr0).congr_of_eventuallyEq hEq (if_pos hb)
  · have hev : ∀ᶠ v in nhdsWithin r (Ici r), ¬ (v.toNNReal : WithTop NNReal) < tau := by
      filter_upwards [self_mem_nhdsWithin (a := r) (s := Ici r)] with v hv
      exact not_lt_of_ge ((le_of_not_gt hb).trans
        (WithTop.coe_le_coe.mpr (Real.toNNReal_le_toNNReal hv)))
    have hEq : (fun v => k v) =ᶠ[nhdsWithin r (Ici r)] fun _ => (0 : ℝ) :=
      hev.mono fun v hv => if_neg hv
    exact continuousWithinAt_const.congr_of_eventuallyEq hEq (if_neg hb)
