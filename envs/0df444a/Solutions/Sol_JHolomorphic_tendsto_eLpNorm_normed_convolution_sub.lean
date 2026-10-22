-- Prove2me | solution 1 for JHolomorphic.tendsto_eLpNorm_normed_convolution_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:30:21.381161+00:00
-- url     : https://prove2.me/submissions/b4e4e0e1-8314-4874-91dc-dfb23f922e86

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Theorems.Thm_JHolomorphic_eLpNorm_normed_convolution_le
import Theorems.Thm_JHolomorphic_tendsto_eLpNorm_normed_convolution_sub_of_continuous
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.MetricSpace.Thickening



namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal

theorem tendsto_eLpNorm_normed_convolution_sub_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {f : ℂ → E} (hf : MemLp f p volume) :
    Tendsto (fun n => eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] f - f) p volume)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun n => by simp [hεt]
  set η := ε / 3 with hηdef
  have hη : η ≠ 0 := (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne'
  obtain ⟨g, hgc, hfg, hg, hgL⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hpt hη
  have hfgL : MemLp (f - g) p volume := hf.sub hgL
  filter_upwards [(ENNReal.tendsto_nhds_zero.1
    (tendsto_eLpNorm_normed_convolution_sub_of_continuous (p := p) φ hφ hg hgc)) η
    (pos_iff_ne_zero.2 hη)] with n hn
  have hbc := (φ n).hasCompactSupport_normed (μ := volume)
  have hbcont := (φ n).continuous_normed (μ := volume)
  have hex1 : ConvolutionExists ((φ n).normed volume) g (lsmul ℝ ℝ) volume :=
    hbc.convolutionExists_left _ hbcont hg.locallyIntegrable
  have hex2 : ConvolutionExists ((φ n).normed volume) (f - g) (lsmul ℝ ℝ) volume :=
    hbc.convolutionExists_left _ hbcont (hfgL.locallyIntegrable hp)
  have hdec : (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] f - f =
      ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) +
        ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (f - g) - (f - g)) := by
    have e : f = g + (f - g) := by abel
    conv_lhs => rw [e]
    rw [hex1.distrib_add hex2]
    abel
  have hm1 : AEStronglyMeasurable ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) volume :=
    ((hbc.continuous_convolution_left _ hbcont hg.locallyIntegrable).sub hg).aestronglyMeasurable
  have hmc2 : AEStronglyMeasurable ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (f - g)) volume :=
    (hbc.continuous_convolution_left _ hbcont (hfgL.locallyIntegrable hp)).aestronglyMeasurable
  rw [hdec]
  calc eLpNorm (((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) +
        ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (f - g) - (f - g))) p volume
      ≤ eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) p volume +
        eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (f - g) - (f - g)) p volume :=
        eLpNorm_add_le hm1 (hmc2.sub hfgL.1) hp
    _ ≤ η + (eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (f - g)) p volume +
        eLpNorm (f - g) p volume) := add_le_add hn (eLpNorm_sub_le hmc2 hfgL.1 hp)
    _ ≤ η + (η + η) := by
        gcongr
        · exact (eLpNorm_normed_convolution_le (φ n) hp hpt hfgL.1).trans hfg
    _ = ε := by rw [← add_assoc, hηdef, ENNReal.add_thirds]

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {f : ℂ → E} (hf : MemLp f p volume) :
    Tendsto (fun n => eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] f - f) p volume)
      atTop (𝓝 0) :=
  tendsto_eLpNorm_normed_convolution_sub_aux hp hpt φ hφ hf
