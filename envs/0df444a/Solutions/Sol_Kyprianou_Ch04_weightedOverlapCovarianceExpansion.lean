-- Prove2me | solution 1 for Kyprianou.Ch04.weightedOverlapCovarianceExpansion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:26:00.814125+00:00
-- url     : https://prove2.me/submissions/ca9ec78b-cce0-4e2f-b29a-e3e08a027e8a

import Mathlib
open MeasureTheory
set_option autoImplicit false
universe u

/-- Covariance of two decomposed counts with a common summand. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W X Y U V Z : Ω → ℝ)
    (hX : X =ᵐ[P] fun ω => U ω + V ω)
    (hY : Y =ᵐ[P] fun ω => V ω + Z ω)
    (hUV : Integrable (fun ω => W ω * U ω * V ω) P)
    (hUZ : Integrable (fun ω => W ω * U ω * Z ω) P)
    (hVZ : Integrable (fun ω => W ω * V ω * Z ω) P)
    (hVV : Integrable (fun ω => W ω * (V ω)^2) P)
    (eUV : (∫ ω, W ω * U ω * V ω ∂P) = 0)
    (eUZ : (∫ ω, W ω * U ω * Z ω ∂P) = 0)
    (eVZ : (∫ ω, W ω * V ω * Z ω ∂P) = 0) :
    (∫ ω, W ω * X ω * Y ω ∂P) =
      ∫ ω, W ω * (V ω)^2 ∂P := by
  calc
    (∫ ω, W ω * X ω * Y ω ∂P) =
        ∫ ω, ((W ω * U ω * V ω + W ω * U ω * Z ω) +
          W ω * V ω * Z ω) + W ω * (V ω)^2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hX, hY] with ω hx hy
      rw [hx, hy]
      ring
    _ = _ := by
      have h1 := integral_add ((hUV.add hUZ).add hVZ) hVV
      have h2 := integral_add (hUV.add hUZ) hVZ
      have h3 := integral_add hUV hUZ
      simp only [Pi.add_apply] at h1 h2 h3
      rw [h1, h2, h3, eUV, eUZ, eVZ]
      simp
