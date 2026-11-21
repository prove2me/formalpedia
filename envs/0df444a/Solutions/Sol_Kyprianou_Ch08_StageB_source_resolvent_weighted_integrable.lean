-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_resolvent_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:57:26.725179+00:00
-- url     : https://prove2.me/submissions/f7d12382-3d6f-442f-a85d-b6969351bd70

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q θ : ℝ)
    (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
      (W 0 x + q * (∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume)))
      (Set.Ioi (0 : ℝ)) volume := by
  have h0 := ((hW 0 (le_refl (0 : ℝ))).2.2.2.2.2 θ hθ hroot0).1
  have hqint := ((hW q hq).2.2.2.2.2 θ hθ hrootq).1
  have hc := AvramDividend.Classical.positive_causal_convolution_laplace_integrable
    (W 0) (W q) θ (by simpa only [neg_mul] using h0)
      (by simpa only [neg_mul] using hqint)
  have hc' : IntegrableOn (fun x : ℝ =>
      Real.exp (-θ * x) * (∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume)) (Set.Ioi (0 : ℝ)) volume := by
    simpa only [neg_mul] using hc
  have heq : (fun x : ℝ => Real.exp (-θ * x) *
      (W 0 x + q * (∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume))) =
      (fun x : ℝ => Real.exp (-θ * x) * W 0 x +
        q * (Real.exp (-θ * x) * (∫ s in Set.Ioc (0 : ℝ) x,
          W 0 s * W q (x - s) ∂volume))) := by
    funext x
    ring
  rw [heq]
  exact h0.add (hc'.const_mul q)
