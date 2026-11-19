-- Prove2me | solution 1 for LevyStochCalc.Probability.norm_toLp_sq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:56:05.052668+00:00
-- url     : https://prove2.me/submissions/f59d5801-a3e3-48e3-ab5b-9dc3aca3dff0

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : Ω → ℂ) (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂P := by
  have h1 : ‖hf.toLp f‖ ^ 2 = RCLike.re (inner ℂ (hf.toLp f) (hf.toLp f)) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h1, L2.inner_def]
  have hae : (fun ω => RCLike.re (inner ℂ ((hf.toLp f) ω) ((hf.toLp f) ω))) =ᵐ[P]
      (fun ω => ‖f ω‖ ^ 2) := by
    filter_upwards [hf.coeFn_toLp] with ω hω
    rw [hω, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [← integral_re (L2.integrable_inner _ _), integral_congr_ae hae]
