-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_resolvent_laplace_scalar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:47:47.433509+00:00
-- url     : https://prove2.me/submissions/603f5402-1259-4b0b-aa29-79c7eb11f4fe

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_product
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hroot0 : Phi ψ 0 < β) (hrootq : Phi ψ q < β) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) * W 0 x ∂volume) +
      q * (∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-(β * x)) *
          (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ∂volume) =
      (ψ β - q)⁻¹ := by
  have h0 := ((hW 0 (le_refl (0 : ℝ))).2.2.2.2.2 β hβ hroot0)
  have hqscale := ((hW q hq).2.2.2.2.2 β hβ hrootq)
  have hprod := AvramDividend.Classical.positive_causal_convolution_laplace_product
    (W 0) (W q) β
    (by simpa only [neg_mul] using h0.1)
    (by simpa only [neg_mul] using hqscale.1)
  have hp : 0 < ψ β :=
    source_scale_laplace_gap_pos ψ W hW 0 β (le_refl (0 : ℝ)) hβ hroot0
  have hd : 0 < ψ β - q :=
    sub_pos.mpr (source_scale_laplace_gap_pos ψ W hW q β hq hβ hrootq)
  have h0mass : (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(β * t)) * W 0 t ∂volume) = (ψ β)⁻¹ := by
    simpa only [neg_mul, sub_zero] using h0.2
  have hqmass : (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(β * t)) * W q t ∂volume) = (ψ β - q)⁻¹ := by
    simpa only [neg_mul] using hqscale.2
  rw [hprod, h0mass, hqmass]
  have hpn : ψ β ≠ 0 := ne_of_gt hp
  have hdn : ψ β - q ≠ 0 := ne_of_gt hd
  field_simp [hpn, hdn]
  ring
