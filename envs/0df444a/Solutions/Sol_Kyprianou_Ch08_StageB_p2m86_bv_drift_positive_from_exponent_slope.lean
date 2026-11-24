-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m86_bv_drift_positive_from_exponent_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:21:17.177911+00:00
-- url     : https://prove2.me/submissions/2c8eaee4-9ce1-4225-9509-2b83e66afaa2

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_laplace_convex
import Mathlib.Analysis.Convex.Slope
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
      0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure := by
  intro Ω mΩ P hP D ψ W hψ hW hbv hlim
  have hzero : ψ 0 = 0 := by
    simpa [SpectrallyNegativeModel.toData] using (hψ 0 1 le_rfl (by norm_num)).2
  have hsc : IsQScale ψ 1 (W 1) := hW 1 (by norm_num)
  have hroot : Phi ψ 1 ∈ RightRootSet ψ 1 := hsc.1.2.1
  have hv : ψ (Phi ψ 1) = 1 := hroot.2
  have hr : 0 < Phi ψ 1 := by
    have hn : 0 ≤ Phi ψ 1 := hroot.1
    by_contra h
    have he : Phi ψ 1 = 0 := le_antisymm (le_of_not_gt h) hn
    rw [he, hzero] at hv
    norm_num at hv
  have hc := source_result81_law_laplace_convex Ω P D ψ hψ
  have hbound : 1 / Phi ψ 1 ≤ bvDrift (-D.triplet.drift) D.triplet.levyMeasure := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (Phi ψ 1)] with β hβ
    have ha : (0 : ℝ) ∈ Ici 0 := by simp
    have hx : Phi ψ 1 ∈ Ici 0 := hr.le
    have hy : β ∈ Ici 0 := hr.le.trans hβ
    have hs := hc.secant_mono ha hx hy (ne_of_gt hr) (ne_of_gt (hr.trans_le hβ)) hβ
    simpa only [hzero, hv, sub_zero] using hs
  exact (div_pos one_pos hr).trans_le hbound
