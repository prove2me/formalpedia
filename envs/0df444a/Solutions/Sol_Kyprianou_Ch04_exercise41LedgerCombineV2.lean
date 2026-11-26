-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41LedgerCombineV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:33:59.25881+00:00
-- url     : https://prove2.me/submissions/6466e6a1-da65-4387-bf64-924fadcfa191

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
set_option autoImplicit false

theorem solution
    {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z)
    (f g a b : ℝ → ℝ)
    (c α β x0 xt D A B : ℝ)
    (pre post : Z → ℝ)
    (hSplit : ∀ x, f x = g x + c + α * a x + β * b x)
    (hg : Integrable (fun z => g (post z) - g (pre z)) μ)
    (ha : Integrable (fun z => a (post z) - a (pre z)) μ)
    (hb : Integrable (fun z => b (post z) - b (pre z)) μ)
    (hG : g xt = g x0 + D + ∫ z, (g (post z) - g (pre z)) ∂μ)
    (hA : a xt = a x0 + (∫ z, (a (post z) - a (pre z)) ∂μ) + A)
    (hB : b xt = b x0 + (∫ z, (b (post z) - b (pre z)) ∂μ) + B) :
    f xt = f x0 + D + (∫ z, (f (post z) - f (pre z)) ∂μ) +
      α * A + β * B := by
  have hd :
      (fun z => f (post z) - f (pre z)) =
      (fun z => (g (post z) - g (pre z)) +
        α * (a (post z) - a (pre z)) +
        β * (b (post z) - b (pre z))) := by
    funext z
    rw [hSplit (post z), hSplit (pre z)]
    ring
  rw [hd]
  have h1 : (∫ z, (g (post z) - g (pre z)) +
        α * (a (post z) - a (pre z)) ∂μ) =
      (∫ z, (g (post z) - g (pre z)) ∂μ) +
        ∫ z, α * (a (post z) - a (pre z)) ∂μ := by
    simpa only [Pi.add_apply] using integral_add hg (ha.const_mul α)
  have h2 : (∫ z, (g (post z) - g (pre z)) +
        α * (a (post z) - a (pre z)) +
        β * (b (post z) - b (pre z)) ∂μ) =
      (∫ z, (g (post z) - g (pre z)) +
        α * (a (post z) - a (pre z)) ∂μ) +
        ∫ z, β * (b (post z) - b (pre z)) ∂μ := by
    simpa only [Pi.add_apply] using
      integral_add (hg.add (ha.const_mul α)) (hb.const_mul β)
  rw [h2, h1]
  rw [integral_const_mul, integral_const_mul]
  rw [hSplit xt, hSplit x0, hG, hA, hB]
  ring
