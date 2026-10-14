-- Prove2me | solution 1 for MeasureTheory.tendsto_eLpNorm_sub_normed_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T22:20:42.17229+00:00
-- url     : https://prove2.me/submissions/008ca137-1955-49b8-ba8b-043810454c1f

import Theorems.Thm_BookProof_MollifierL2_tendsto_translate_Lp
import Theorems.Thm_MeasureTheory_eLpNorm_sub_convolution_le_of_support
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory Filter ContinuousLinearMap Metric
open scoped Convolution Topology

theorem solution {n : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : MemLp d p volume) :
    Tendsto (fun m => eLpNorm (d - ((φ m).normed volume ⋆[lsmul ℝ ℝ, volume] d)) p volume)
      atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have ht := BookProof.MollifierL2.tendsto_translate_Lp hp0 hptop hp hd
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  have he : ∀ᶠ y : EuclideanSpace ℝ (Fin n) in 𝓝 0,
      eLpNorm (fun x => d (x - y) - d x) p volume ≤ ε :=
    (ENNReal.tendsto_nhds_zero.1 ht) ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 he
  have hr : ∀ᶠ m in atTop, (φ m).rOut < δ :=
    hφ.eventually (gt_mem_nhds hδ)
  filter_upwards [hr] with m hm
  apply MeasureTheory.eLpNorm_sub_convolution_le_of_support hp hptop
    ((φ m).normed volume) (φ m).continuous_normed (φ m).hasCompactSupport_normed
    (φ m).nonneg_normed (φ m).integral_normed d hd ε
  intro y hy
  apply hball
  have hy' : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (φ m).rOut := by
    rwa [(φ m).support_normed_eq] at hy
  exact (mem_ball.1 hy').trans hm
