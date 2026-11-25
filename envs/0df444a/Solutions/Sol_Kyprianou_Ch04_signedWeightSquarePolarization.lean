-- Prove2me | solution 1 for Kyprianou.Ch04.signedWeightSquarePolarization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:55:32.741412+00:00
-- url     : https://prove2.me/submissions/50f24d27-5058-43d3-aba1-80add32bb0f1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
set_option autoImplicit false
universe u

/-- Polarisation with an integrable signed weight and additive second moments. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W A B C : Ω → ℝ)
    (hA : Integrable (fun ω => W ω * (A ω)^2) P)
    (hB : Integrable (fun ω => W ω * (B ω)^2) P)
    (hC : Integrable (fun ω => W ω * (C ω)^2) P)
    (hAdd : C =ᵐ[P] (fun ω => A ω + B ω))
    (hVar : (∫ ω, W ω * (C ω)^2 ∂P) =
      (∫ ω, W ω * (A ω)^2 ∂P) + (∫ ω, W ω * (B ω)^2 ∂P)) :
    (∫ ω, W ω * A ω * B ω ∂P) = 0 := by
  have heq : (fun ω => W ω * A ω * B ω) =ᵐ[P]
      (fun ω => (1/2 : ℝ) * (W ω * (C ω)^2 -
        W ω * (A ω)^2 - W ω * (B ω)^2)) := by
    filter_upwards [hAdd] with ω hω
    rw [hω]
    ring
  rw [integral_congr_ae heq, integral_const_mul]
  have hsub : Integrable (fun ω => W ω * (C ω)^2 - W ω * (A ω)^2) P :=
    hC.sub hA
  rw [integral_sub hsub hB, integral_sub hC hA, hVar]
  ring
