-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_upper_exit_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:48:08.305543+00:00
-- url     : https://prove2.me/submissions/d7269101-b8a0-411f-bac5-a56538d5f8f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_series_entire
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_convolution_series
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_positive_discount
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_payoff_continuous_zero
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_exists_positive
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem source_scale_family_unique_at_discount
    (ψ : ℝ → ℝ) (W V : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (hV : HasSourceScaleFamily ψ V)
    (q : ℝ) (hq : 0 ≤ q) :
    W q = V q := by
  obtain ⟨_, hnegW, hnonW, hcontW, _, hlapW⟩ := hW q hq
  obtain ⟨_, hnegV, hnonV, hcontV, _, hlapV⟩ := hV q hq
  have hpos : ∀ x : ℝ, 0 < x → W q x = V q x := by
    refine AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq
      (W q) (V q) (max 0 (Phi ψ q)) (hcontW.mono Ioi_subset_Ici_self)
      (hcontV.mono Ioi_subset_Ici_self) (fun x _ => hnonW x) (fun x _ => hnonV x) ?_
    intro θ hθ
    have hθ0 : 0 ≤ θ := (le_max_left (0 : ℝ) (Phi ψ q)).trans hθ.le
    have hθΦ : Phi ψ q < θ := lt_of_le_of_lt (le_max_right _ _) hθ
    obtain ⟨hIW, hLW⟩ := hlapW θ hθ0 hθΦ
    obtain ⟨hIV, hLV⟩ := hlapV θ hθ0 hθΦ
    exact ⟨hIW, hIV, hLW.trans hLV.symm⟩
  funext x
  rcases lt_trichotomy x 0 with h | h | h
  · rw [hnegW x h, hnegV x h]
  · subst x
    haveI : (nhdsWithin (0 : ℝ) (Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
    have hW0 : Tendsto (W q) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (W q 0)) :=
      (hcontW 0 (by simp)).mono Ioi_subset_Ici_self
    have hV0 : Tendsto (V q) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (V q 0)) :=
      (hcontV 0 (by simp)).mono Ioi_subset_Ici_self
    exact tendsto_nhds_unique hW0 (hV0.congr' (by
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with z hz
      exact (hpos z hz).symm))
  · exact hpos x h

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


theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    upBeforeDownExpectation P D.X q x a = W q x / W q a := by
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    obtain ⟨V, hV, hVpos⟩ := source_result81_scale_exists_positive Ω P D ψ hψ
    have hWV := source_scale_family_unique_at_discount ψ W V hW hV 0 le_rfl
    have hWa : 0 < W 0 a := by
      rw [hWV]
      exact hVpos 0 a le_rfl ha
    have hwx : Tendsto (fun r => W r x) (nhdsWithin 0 (Ioi 0)) (nhds (W 0 x)) :=
      (scale_continuousWithinAt_in_discount ψ W hW x 0 le_rfl).mono Ioi_subset_Ici_self
    have hwa : Tendsto (fun r => W r a) (nhdsWithin 0 (Ioi 0)) (nhds (W 0 a)) :=
      (scale_continuousWithinAt_in_discount ψ W hW a 0 le_rfl).mono Ioi_subset_Ici_self
    have hpayoff := source_result81_upper_payoff_continuous_zero Ω P D x a
    exact tendsto_nhds_unique hpayoff ((hwx.div hwa (ne_of_gt hWa)).congr' (by
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with r hr
      exact (source_result81_upper_positive_discount Ω P D ψ hψ W hW r x a hr ha hxa).symm))
  · exact source_result81_upper_positive_discount Ω P D ψ hψ W hW q x a hpos ha hxa
