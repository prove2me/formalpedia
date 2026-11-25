-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothParam.contDiff_integral_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:05.026469+00:00
-- url     : https://prove2.me/submissions/771daf55-88cd-4198-bfc4-839be0dadde2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_hasFDerivAt_partial
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_pderiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_integrable_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_hasFDerivAt_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothParam
variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory.CompanionTheory.SmoothParam
theorem _root_.solution (Ω P Y : Type) [MeasurableSpace Ω] [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (ν : Measure Ω) (w : Ω → ℂ) (ψ : Ω → Y) (K : Set Y)
    (hw : Integrable w ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (h : P × Y → ℂ) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p => ∫ x, h (p, ψ x) * w x ∂ν) ∧
      ∀ p v, fderiv ℝ (fun q => ∫ x, h (q, ψ x) * w x ∂ν) p v
        = ∫ x, fderiv ℝ (fun q => h (q, ψ x)) p v * w x ∂ν := by
  have hu₁ : Integrable (fun x => (w x).re) ν := hw.re
  have hu₂ : Integrable (fun x => (w x).im) ν := hw.im
  set h₂ : P × Y → ℂ := fun z => Complex.I * h z with hh₂def
  have hh₂ : ContDiff ℝ ∞ h₂ := contDiff_const.mul hh
  have hdec : ∀ (a b : ℂ), a * b = b.re • a + b.im • (Complex.I * a) := by
    intro a b
    apply Complex.ext <;> simp <;> ring
  have hsplit : (fun p => ∫ x, h (p, ψ x) * w x ∂ν)
      = fun p => (∫ x, (w x).re • h (p, ψ x) ∂ν) + ∫ x, (w x).im • h₂ (p, ψ x) ∂ν := by
    funext p
    rw [← integral_add (integrable_weight hu₁ hψ hK hψK hh.continuous p)
      (integrable_weight hu₂ hψ hK hψK hh₂.continuous p)]
    exact integral_congr_ae (Eventually.of_forall fun x => hdec _ _)
  refine ⟨?_, fun p v => ?_⟩
  · rw [hsplit]
    exact (contDiff_weight hu₁ hψ hK hψK hh).add (contDiff_weight hu₂ hψ hK hψK hh₂)
  · have hd : Differentiable ℝ h := hh.differentiable (by simp)
    have hD := (hasFDerivAt_weight hu₁ hψ hK hψK hh p).add
      (hasFDerivAt_weight hu₂ hψ hK hψK hh₂ p)
    have hfd := hD.fderiv
    have hi₁ := integrable_weight hu₁ hψ hK hψK (contDiff_pderiv hh).continuous p
    have hi₂ := integrable_weight hu₂ hψ hK hψK (contDiff_pderiv hh₂).continuous p
    have hp₂ : ∀ y, pderiv h₂ (p, y) v = Complex.I * pderiv h (p, y) v := by
      intro y
      have h1 : HasFDerivAt (fun q => h (q, y)) (pderiv h (p, y)) p :=
        ((hasFDerivAt_partial hd p y).differentiableAt).hasFDerivAt
      have h2 : HasFDerivAt (fun q => h₂ (q, y)) (Complex.I • pderiv h (p, y)) p := by
        exact h1.const_smul Complex.I
      have : pderiv h₂ (p, y) = Complex.I • pderiv h (p, y) := h2.fderiv
      rw [this]; simp
    rw [hsplit]
    change fderiv ℝ ((fun p => ∫ x, (w x).re • h (p, ψ x) ∂ν) +
      (fun p => ∫ x, (w x).im • h₂ (p, ψ x) ∂ν)) p v = _
    rw [hfd, ContinuousLinearMap.add_apply, ContinuousLinearMap.integral_apply hi₁,
      ContinuousLinearMap.integral_apply hi₂,
      ← integral_add (hi₁.apply_continuousLinearMap v) (hi₂.apply_continuousLinearMap v)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.smul_apply]
    rw [hp₂]
    exact (hdec _ _).symm
end GlobalTheory.CompanionTheory.SmoothParam
