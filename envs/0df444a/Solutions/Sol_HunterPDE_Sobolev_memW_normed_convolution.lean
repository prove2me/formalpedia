-- Prove2me | solution 1 for HunterPDE.Sobolev.memW_normed_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:03:28.594949+00:00
-- url     : https://prove2.me/submissions/0adb477e-4d91-4464-a345-c486197128ed

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_convolution_testFunction
import Theorems.Thm_MeasureTheory_eLpNorm_convolution_le_of_nonneg_normalized
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

open MeasureTheory Filter ContinuousLinearMap HunterPDE.Sobolev
open scoped Convolution Topology

theorem solution {n k : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f) :
    MemW k p Set.univ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) := by
  have hc : Continuous (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) :=
    φ.hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ)
      φ.continuous_normed (locallyIntegrableOn_univ.mp hf.1)
  refine ⟨locallyIntegrableOn_univ.mpr hc.locallyIntegrable, ?_⟩
  intro α hα
  obtain ⟨d, hd, hdp⟩ := hf.2 α hα
  have hdp' : MemLp d p volume := by simpa only [Measure.restrict_univ] using hdp
  have hρ : IsTestFunction Set.univ (φ.normed volume) :=
    ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, Set.subset_univ _⟩
  refine ⟨φ.normed volume ⋆[lsmul ℝ ℝ, volume] d,
    hd.convolution_testFunction (φ.normed volume) hρ, ?_⟩
  have hdc : Continuous (φ.normed volume ⋆[lsmul ℝ ℝ, volume] d) :=
    φ.hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ)
      φ.continuous_normed (hdp'.locallyIntegrable hp)
  have hbound := MeasureTheory.eLpNorm_convolution_le_of_nonneg_normalized hp hptop
    (φ.normed volume) φ.continuous_normed φ.hasCompactSupport_normed
    φ.nonneg_normed φ.integral_normed d hdp'
  simpa only [Measure.restrict_univ] using
    (show MemLp (φ.normed volume ⋆[lsmul ℝ ℝ, volume] d) p volume from
      ⟨hdc.aestronglyMeasurable, hbound.trans_lt hdp'.eLpNorm_lt_top⟩)
