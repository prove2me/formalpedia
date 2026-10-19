-- Prove2me | solution 1 for HunterPDE.Sobolev.exists_smooth_approx_with_halfSpace_gap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T09:55:14.953889+00:00
-- url     : https://prove2.me/submissions/92e0b794-a13d-405d-b371-b860f5609d6f

import Theorems.Thm_HunterPDE_Sobolev_memW_translate
import Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_translation_small
import Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_sub_triangle
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.Tactic.Linarith
import Theorems.Thm_HunterPDE_Sobolev_memW_normed_convolution
import Theorems.Thm_HunterPDE_Sobolev_eLpNorm_weakDeriv_sub_normed_convolution
import Theorems.Thm_MeasureTheory_tendsto_eLpNorm_sub_normed_convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Positivity

open MeasureTheory Filter ContinuousLinearMap
open HunterPDE.Sobolev
open scoped Convolution Topology ENNReal NNReal

open HunterPDE.Compactness
set_option autoImplicit false

-- Translate inward by r/2, then mollify at radius below r/4.
-- The support estimate uses Haar invariance to transport the a.e. vanishing hypothesis.
theorem solution {m k : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hF : HunterPDE.Sobolev.MemW k p Set.univ F)
    (hsupport : ∀ᵐ x ∂volume, x ∉ closedUpperHalfSpace m → F x = 0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (δ : ℝ),
      0 < δ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      HunterPDE.Sobolev.MemW k p Set.univ g ∧
      tsupport g ⊆ {x | δ ≤ x (Fin.last m)} ∧
      HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - g) < ε := by
  classical
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨r, hr, hsmall⟩ := sobolevNorm_translation_small hp hp' F hF (ε / 2) hhalf
  let a : EuclideanSpace ℝ (Fin (m + 1)) := EuclideanSpace.single (Fin.last m) (r / 2)
  have ha : ‖a‖ < r := by
    simp only [a, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  let f := fun x => F (x - a)
  have hf : HunterPDE.Sobolev.MemW k p Set.univ f := memW_translate F hF a
  have hFf : HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - f) < ε / 2 := hsmall a ha
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin (m + 1))) := fun m =>
    { rIn := (1 / ((m : ℝ) + 1)) / 2
      rOut := 1 / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by exact half_lt_self (by positivity) }
  have hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let g : ℕ → EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun m =>
    (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] f
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp'
  have hd : ∀ α ∈ multiIndices (m + 1) k,
      Tendsto (fun m => eLpNorm (weakDeriv Set.univ α (f - g m)) p volume) atTop (𝓝 0) := by
    intro α hα
    have hαk : ∑ i, α i ≤ k := (Finset.mem_filter.mp hα).2
    obtain ⟨d, hd, hdp⟩ := hf.2 α hαk
    have hdp' : MemLp d p volume := by simpa using hdp
    have heq : ∀ q, eLpNorm (weakDeriv Set.univ α (f - g q)) p volume =
        eLpNorm (d - ((φ q).normed volume ⋆[lsmul ℝ ℝ, volume] d)) p volume := by
      intro q
      exact eLpNorm_weakDeriv_sub_normed_convolution hp hp' (φ q) f hf α hαk d hd hdp'
    simp_rw [heq]
    exact tendsto_eLpNorm_sub_normed_convolution hp hp' φ hφ d hdp'
  have hs : Tendsto (fun q => ∑ α ∈ multiIndices (m + 1) k,
      eLpNorm (weakDeriv Set.univ α (f - g q)) p volume ^ p.toReal) atTop (𝓝 0) := by
    have H := tendsto_finsetSum (multiIndices (m + 1) k) (fun α hα => (hd α hα).ennrpow_const p.toReal)
    simpa [ENNReal.zero_rpow_of_pos hpr] using H
  have hn : Tendsto (fun m => HunterPDE.Sobolev.sobolevNorm k p Set.univ (f - g m)) atTop (𝓝 0) := by
    simpa [HunterPDE.Sobolev.sobolevNorm, hp', Measure.restrict_univ,
      ENNReal.zero_rpow_of_pos (inv_pos.mpr hpr)] using hs.ennrpow_const (1 / p.toReal)
  have hrad : ∀ᶠ j in atTop, (φ j).rOut < r / 4 :=
    hφ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 4))
  obtain ⟨j, hj, hjr⟩ := ((hn.eventually (gt_mem_nhds hhalf)).and hrad).exists
  have hgW : HunterPDE.Sobolev.MemW k p Set.univ (g j) := memW_normed_convolution hp hp' (φ j) f hf
  refine ⟨g j, r / 4, by linarith, ?_, hgW, ?_, ?_⟩
  · exact (φ j).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ j).contDiff_normed (locallyIntegrableOn_univ.mp hf.1)
  · have hz : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), x (Fin.last m) < r / 4 → g j x = 0 := by
      intro x hx
      rw [show g j x = ∫ y, (lsmul ℝ ℝ) ((φ j).normed volume y) (F (x - y - a)) by rfl]
      apply integral_eq_zero_of_ae
      have hs := ((measurePreserving_sub_right volume a).comp
        (Measure.measurePreserving_sub_left volume x)).quasiMeasurePreserving.ae hsupport
      filter_upwards [hs] with y hy
      by_cases hyφ : (φ j).normed volume y = 0
      · simp [hyφ]
      · have hyball : y ∈ Metric.ball 0 (φ j).rOut :=
          (φ j).support_normed_eq (μ := (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))) ▸ hyφ
        have hyn : ‖y‖ < r / 4 := lt_trans (by simpa [dist_zero_right] using hyball) hjr
        have hycoord : |y (Fin.last m)| ≤ ‖y‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y (Fin.last m)
        have hcoord : (x - y - a) (Fin.last m) < 0 := by
          simp only [a, PiLp.sub_apply, EuclideanSpace.single, PiLp.single_apply, ite_true]
          have := neg_abs_le (y (Fin.last m))
          linarith
        have hzero : F (x - y - a) = 0 :=
          hy (by simpa [HunterPDE.Compactness.closedUpperHalfSpace] using not_le.mpr hcoord)
        simp [hzero]
    apply closure_minimal
    · intro x hx
      exact le_of_not_gt (fun h => hx (hz x h))
    · exact isClosed_le continuous_const (by fun_prop)
  · calc
      HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - g j) ≤
          HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - f) + HunterPDE.Sobolev.sobolevNorm k p Set.univ (f - g j) :=
        sobolevNorm_sub_triangle hp hp' Set.univ isOpen_univ F f (g j) hF hf hgW
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hFf hj
      _ = ε := ENNReal.add_halves ε
