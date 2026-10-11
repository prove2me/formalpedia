-- Prove2me | solution 1 for HunterPDE.Sobolev.smooth_approximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:42:48.629331+00:00
-- url     : https://prove2.me/submissions/fb9dca92-fafd-4dde-9c02-346958f8acdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HunterPDE_Sobolev_memW_normed_convolution
import Theorems.Thm_HunterPDE_Sobolev_eLpNorm_weakDeriv_sub_normed_convolution
import Theorems.Thm_MeasureTheory_tendsto_eLpNorm_sub_normed_convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Positivity

open MeasureTheory Filter ContinuousLinearMap
open HunterPDE.Sobolev
open scoped Convolution Topology

theorem solution {n k : ℕ}
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ MemW k p Set.univ g ∧
        sobolevNorm k p Set.univ (f - g) < ε := by
  classical
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    { rIn := (1 / ((m : ℝ) + 1)) / 2
      rOut := 1 / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by exact half_lt_self (by positivity) }
  have hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] f
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hptop
  have hd : ∀ α ∈ multiIndices n k,
      Tendsto (fun m => eLpNorm (weakDeriv Set.univ α (f - g m)) p volume) atTop (𝓝 0) := by
    intro α hα
    have hαk : ∑ i, α i ≤ k := (Finset.mem_filter.mp hα).2
    obtain ⟨d, hd, hdp⟩ := hf.2 α hαk
    have hdp' : MemLp d p volume := by simpa using hdp
    have heq : ∀ m, eLpNorm (weakDeriv Set.univ α (f - g m)) p volume =
        eLpNorm (d - ((φ m).normed volume ⋆[lsmul ℝ ℝ, volume] d)) p volume := by
      intro m
      exact eLpNorm_weakDeriv_sub_normed_convolution hp hptop (φ m) f hf α hαk d hd hdp'
    simp_rw [heq]
    exact tendsto_eLpNorm_sub_normed_convolution hp hptop φ hφ d hdp'
  have hs : Tendsto (fun m => ∑ α ∈ multiIndices n k,
      eLpNorm (weakDeriv Set.univ α (f - g m)) p volume ^ p.toReal) atTop (𝓝 0) := by
    have H := tendsto_finsetSum (multiIndices n k) (fun α hα => (hd α hα).ennrpow_const p.toReal)
    simpa [ENNReal.zero_rpow_of_pos hpr] using H
  have hn : Tendsto (fun m => sobolevNorm k p Set.univ (f - g m)) atTop (𝓝 0) := by
    simpa [sobolevNorm, hptop, Measure.restrict_univ,
      ENNReal.zero_rpow_of_pos (inv_pos.mpr hpr)] using hs.ennrpow_const (1 / p.toReal)
  obtain ⟨m, hm⟩ := (hn.eventually (gt_mem_nhds hε)).exists
  refine ⟨g m, ?_, memW_normed_convolution hp hptop (φ m) f hf, hm⟩
  exact (φ m).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (φ m).contDiff_normed (locallyIntegrableOn_univ.mp hf.1)
