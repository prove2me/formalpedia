-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_integral_cutoff_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:34:29.683743+00:00
-- url     : https://prove2.me/submissions/8009ca2c-284e-4c60-a24e-9600d90fdc3c

import Mathlib
open MeasureTheory
set_option autoImplicit false

/-- The difference of an uncut excess and its retained cutoff is the complementary integral. -/
theorem solution {α : Type} [MeasurableSpace α] (μ : Measure α)
    (A B chi : α → ℝ) (hA : Integrable A μ) (hB : Integrable B μ)
    (hTail : Integrable (fun z => (A z-B z)*(1-chi z)) μ) :
    (∫ z, A z ∂μ) - (∫ z, B z ∂μ) -
      (∫ z, (A z-B z)*chi z ∂μ) =
        ∫ z, (A z-B z)*(1-chi z) ∂μ := by
  have he : (fun z => (A z-B z)*chi z) =
      fun z => (A z-B z) - (A z-B z)*(1-chi z) := by
    funext z
    ring
  rw [he]
  have H : (∫ z, A z-B z-(A z-B z)*(1-chi z) ∂μ) =
      (∫ z, A z-B z ∂μ) - ∫ z, (A z-B z)*(1-chi z) ∂μ :=
    integral_sub (hA.sub hB) hTail
  rw [H,integral_sub hA hB]
  ring
