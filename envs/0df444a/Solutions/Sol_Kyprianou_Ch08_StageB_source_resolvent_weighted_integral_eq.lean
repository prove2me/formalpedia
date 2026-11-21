-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_resolvent_weighted_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:58:18.501077+00:00
-- url     : https://prove2.me/submissions/1562e611-bcda-4832-b9a4-7181dce03417

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_resolvent_laplace_scalar
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q θ : ℝ)
    (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) * W q x ∂volume) =
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) *
      (W 0 x + q * (∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume)) ∂volume) := by
  have h0 := ((hW 0 (le_refl (0 : ℝ))).2.2.2.2.2 θ hθ hroot0)
  have hqscale := ((hW q hq).2.2.2.2.2 θ hθ hrootq)
  have hc := AvramDividend.Classical.positive_causal_convolution_laplace_integrable
    (W 0) (W q) θ
    (by simpa only [neg_mul] using h0.1)
    (by simpa only [neg_mul] using hqscale.1)
  have hc' : IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
      (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume))
      (Set.Ioi (0 : ℝ)) volume := by
    simpa only [neg_mul] using hc
  have hdist :
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) *
        (W 0 x + q * (∫ s in Set.Ioc (0 : ℝ) x,
          W 0 s * W q (x - s) ∂volume)) ∂volume) =
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) * W 0 x ∂volume) +
      q * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) *
        (∫ s in Set.Ioc (0 : ℝ) x,
          W 0 s * W q (x - s) ∂volume) ∂volume) := by
    have heq : (fun x : ℝ => Real.exp (-θ * x) * (W 0 x +
        q * (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume))) =
      (fun x : ℝ => Real.exp (-θ * x) * W 0 x +
        q * (Real.exp (-θ * x) * (∫ s in Set.Ioc (0 : ℝ) x,
          W 0 s * W q (x - s) ∂volume))) := by
      funext x
      ring
    rw [heq, integral_add h0.1 (hc'.const_mul q), integral_const_mul]
  rw [hdist]
  have hscalar :
      (ψ θ - q)⁻¹ =
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) * W 0 x ∂volume) +
        q * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) *
          (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ∂volume) := by
    simpa only [neg_mul] using
      (source_scale_resolvent_laplace_scalar ψ W hW q θ hq hθ hroot0 hrootq).symm
  exact hqscale.2.trans hscalar
