-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_one_sided_passage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:33:40.790744+00:00
-- url     : https://prove2.me/submissions/a18a9dbc-85c0-4f95-8eeb-c01e48c88a48

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_down_positive_discount
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_down_payoff_continuous_zero
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_phi_quotient_at_zero
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_series_entire
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_convolution_series
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_convolution_series_entire
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_convolution_series_agrees

open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem scale_continuousWithinAt_in_discount
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hq : 0 ≤ q) :
    ContinuousWithinAt (fun r : ℝ => W r x) (Ici 0) q := by
  by_cases hx : 0 ≤ x
  · let F : ℂ → ℂ := fun z =>
      ∑' n : ℕ, z ^ n * ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)
    have hF : Continuous F :=
      (source_scale_convolution_series_entire ψ W hW x hx).continuous
    have hG : Continuous (fun r : ℝ => (F (r : ℂ)).re) :=
      Complex.continuous_re.comp (hF.comp Complex.continuous_ofReal)
    have hagree : ∀ r ∈ Ici (0 : ℝ), W r x = (F (r : ℂ)).re := by
      intro r hr
      simpa only [F, Complex.ofReal_re] using
        congrArg Complex.re (source_scale_discount_convolution_series ψ W hW x r hx hr)
    exact hG.continuousWithinAt.congr hagree (hagree q hq)
  · have hneg : x < 0 := lt_of_not_ge hx
    have hagree : ∀ r ∈ Ici (0 : ℝ), W r x = (0 : ℝ) := by
      intro r hr
      exact (hW r hr).2.1 x hneg
    exact continuous_const.continuousWithinAt.congr hagree (hagree q hq)

private theorem zscale_continuousWithinAt_in_discount_of_pos
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    ContinuousWithinAt (fun r : ℝ => Zscale r (W r) x) (Ici 0) q := by
  let F : ℂ → ℂ := fun z => 1 + z * ∑' n : ℕ, z ^ n *
    (((∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)
  have hF : Continuous F :=
    (source_zscale_convolution_series_entire ψ W hW x hx).continuous
  have hG : Continuous (fun r : ℝ => (F (r : ℂ)).re) :=
    Complex.continuous_re.comp (hF.comp Complex.continuous_ofReal)
  have hagree : ∀ r ∈ Ici (0 : ℝ), Zscale r (W r) x = (F (r : ℂ)).re := by
    intro r hr
    simpa only [F, Complex.ofReal_re] using
      (congrArg Complex.re (source_zscale_convolution_series_agrees ψ W hW x hx r hr)).symm
  exact hG.continuousWithinAt.congr hagree (hagree q hq)

private theorem zscale_eq_one_of_nonpos
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : x ≤ 0) :
    Zscale q (W q) x = 1 := by
  have hvanish : W q =ᵐ[volume.restrict (Ioc x 0)] fun _ => 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with y hy hne
    exact (hW q hq).2.1 y (lt_of_le_of_ne hy.2 hne)
  rw [Zscale, intervalIntegral.integral_of_ge hx, integral_congr_ae hvanish]
  simp

private theorem zscale_tendsto_one_at_zero
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (x : ℝ) :
    Tendsto (fun q => Zscale q (W q) x) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  by_cases hx : 0 < x
  · have h := (zscale_continuousWithinAt_in_discount_of_pos ψ W hW x 0 hx le_rfl).mono
      (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0)
    have hz : Zscale 0 (W 0) x = 1 := by simp [Zscale]
    change Tendsto (fun q => Zscale q (W q) x) (nhdsWithin 0 (Ioi 0))
      (nhds (Zscale 0 (W 0) x)) at h
    rwa [hz] at h
  · exact tendsto_const_nhds.congr'
      (Filter.Eventually.mono (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))) fun q hq =>
        (zscale_eq_one_of_nonpos ψ W hW q x (le_of_lt hq) (le_of_not_gt hx)).symm)

private theorem one_sided_at_zero_of_coefficient
    (ψ : ℝ → ℝ) (W F : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (x c : ℝ)
    (hpositive : ∀ q : ℝ, 0 < q →
      F q x = Zscale q (W q) x - q / Phi ψ q * W q x)
    (hF : Tendsto (fun q => F q x) (nhdsWithin 0 (Ioi 0)) (nhds (F 0 x)))
    (hc : Tendsto (fun q => q / Phi ψ q) (nhdsWithin 0 (Ioi 0)) (nhds c)) :
    F 0 x = 1 - c * W 0 x := by
  have hWzero : Tendsto (fun q => W q x) (nhdsWithin 0 (Ioi 0)) (nhds (W 0 x)) :=
    (scale_continuousWithinAt_in_discount ψ W hW x 0 le_rfl).mono Ioi_subset_Ici_self
  have hZ := zscale_tendsto_one_at_zero ψ W hW x
  exact tendsto_nhds_unique hF ((hZ.sub (hc.mul hWzero)).congr'
    (Filter.Eventually.mono (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))) fun q hq => (hpositive q hq).symm))

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    (∀ q x : ℝ, 0 < q →
      downExpectation P D.X q x = Zscale q (W q) x - q / Phi ψ q * W q x) ∧
    (∀ x d : ℝ, HasPositiveFiniteRightPsiSlope ψ d →
      downExpectation P D.X 0 x = 1 - d * W 0 x) ∧
    ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
      ∀ x : ℝ, downExpectation P D.X 0 x = 1) := by
  have hPos := source_result81_down_positive_discount Ω P D ψ hψ W hW
  have hLimit := source_result81_down_payoff_continuous_zero Ω P D
  obtain ⟨hSlope, hNoSlope⟩ := source_result81_phi_quotient_at_zero Ω P D ψ hψ W hW
  refine ⟨fun q x hq => hPos q x hq, ?_, ?_⟩
  · intro x d hd
    exact one_sided_at_zero_of_coefficient ψ W (downExpectation P D.X) hW x d
      (fun q hq => hPos q x hq) (hLimit x) (hSlope d hd)
  · intro hs x
    simpa using one_sided_at_zero_of_coefficient ψ W (downExpectation P D.X) hW x 0
      (fun q hq => hPos q x hq) (hLimit x) (hNoSlope hs)
