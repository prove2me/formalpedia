-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_zero_discount_coefficient_match
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:00:02.636534+00:00
-- url     : https://prove2.me/submissions/bad8139f-0b85-40d9-b42b-578920cf5360
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_phi_quotient_at_zero
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_laplace_convex
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_source_scale_cumulative_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_cumulative_reciprocal_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_root_slope_sequence
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_root_mass_match
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_positive_root_coefficient_zero
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) :
    ∃ c : ℝ,
      Tendsto (fun q : ℝ => q / Phi ψ q) (nhdsWithin 0 (Ioi 0)) (𝓝 c) ∧
      Tendsto (fun z : ℝ => Zscale 0 (W 0) z / W 0 z) atTop (𝓝 c) := by
  obtain ⟨hd, hn⟩ := source_result81_phi_quotient_at_zero Ω P D ψ hψ W hW
  have hex : ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun q : ℝ => q / Phi ψ q)
      (nhdsWithin 0 (Ioi 0)) (𝓝 c) := by
    by_cases h : ∃ d, HasPositiveFiniteRightPsiSlope ψ d
    · obtain ⟨d,h⟩ := h
      exact ⟨d,h.1.le,hd d h⟩
    · exact ⟨0,le_rfl,hn h⟩
  obtain ⟨c,hc,hlim⟩ := hex
  refine ⟨c,hlim,?_⟩
  simp only [Zscale, zero_mul, add_zero, one_div]
  obtain ⟨ν,hs,hf,hlap,hV⟩ := p2m85_source_scale_cumulative_nonnegative D ψ W hψ hW 0 le_rfl
  obtain ⟨n,_,hr,_,_⟩ := source_result8_2_v2 Ω P D ψ W hψ hW 0 le_rfl
  have hp : ν univ ≠ 0 := by
    intro h
    have h1 : ν (Iic 1) = 0 := measure_mono_null (subset_univ _) h
    have h' := hV 1
    rw [h1, ENNReal.toReal_zero] at h'
    exact (mul_pos (Real.exp_pos _) (hr.1 1 zero_lt_one)).ne' h'
  have hφ := (hW 0 le_rfl).1.2.1.1
  have hrec := p2m85_cumulative_reciprocal_limit ν (W 0) (Phi ψ 0) hφ hf hp hV
  rcases hφ.eq_or_lt with he | he
  · have hzero : ψ 0 = 0 := by
      simpa [SpectrallyNegativeModel.toData] using (hψ 0 1 le_rfl (by norm_num)).2
    have hseq := p2m85_zero_root_slope_sequence ψ W hW
      (source_result81_law_laplace_convex Ω P D ψ hψ) hzero he.symm c hlim
    have hm := p2m85_zero_root_mass_match ν ψ c hs
      (fun s hs => source_scale_laplace_gap_pos ψ W hW 0 s le_rfl hs.le
        (by rw [← he]; exact hs))
      (by simpa only [← he, zero_add, sub_zero] using hlap) hseq
    rwa [if_pos he.symm, hm, ENNReal.toReal_ofReal hc] at hrec
  · have hz := p2m85_positive_root_coefficient_zero D ψ W hψ hW c he hlim
    rw [if_neg he.ne'] at hrec
    exact hz.symm ▸ hrec
