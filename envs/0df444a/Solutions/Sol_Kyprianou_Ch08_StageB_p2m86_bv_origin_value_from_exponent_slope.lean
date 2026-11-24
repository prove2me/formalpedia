-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m86_bv_origin_value_from_exponent_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:26:27.001796+00:00
-- url     : https://prove2.me/submissions/265287b6-e2dc-4376-98af-7248143378b7

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_laplace_endpoint_of_isQScale
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ => ψ β / β) atTop
        (𝓝 (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)) →
      0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure →
      W 0 0 = (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)⁻¹ := by
  intro Ω mΩ P hP D ψ W hψ hW hbv hlim hpos
  let d := bvDrift (-D.triplet.drift) D.triplet.levyMeasure
  have hd : d ≠ 0 := ne_of_gt hpos
  have hrec : Tendsto (fun β : ℝ => β * (ψ β)⁻¹) atTop (𝓝 d⁻¹) := by
    have he : (fun β : ℝ => (ψ β / β)⁻¹) =
        (fun β : ℝ => β * (ψ β)⁻¹) := by
      funext β
      rw [inv_div, div_eq_mul_inv]
    rw [← he]
    exact hlim.inv₀ hd
  have hsc : IsQScale ψ 0 (W 0) := hW 0 le_rfl
  let b : ℝ := max (Phi ψ 0) 0 + 1
  have hb : 0 < b := by
    dsimp [b]
    linarith [le_max_right (Phi ψ 0) (0 : ℝ)]
  have hr : Phi ψ 0 < b := by
    dsimp [b]
    linarith [le_max_left (Phi ψ 0) (0 : ℝ)]
  exact AvramDividend.Classical.laplace_endpoint_of_isQScale ψ (W 0)
    b d⁻¹ hb hr (inv_ne_zero hd) hsc hrec
