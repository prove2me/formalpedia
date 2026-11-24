-- Prove2me | solution 1 for GlobalTheory.GallagherLemma.fourier_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:09.450007+00:00
-- url     : https://prove2.me/submissions/96b03546-a2c1-4595-a34d-ae3eea8497bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Theorems.Thm_GlobalTheory_GallagherLemma_continuous_fourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma
namespace GlobalTheory.GallagherLemma
theorem _root_.solution {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  refine ae_eq_of_integral_contDiff_smul_eq (continuous_fourier hf).locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ?_
  intro g hg hc
  have hc' : HasCompactSupport (fun x => (g x : ℂ)) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hg' := Complex.ofRealCLM.contDiff.comp hg
  set φ : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hg' with hφ
  have hφx : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 := congrArg (fun D => D φ) (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
  have h3 : ∫ x, (𝓕 φ) x • f x = ∫ x, φ x • 𝓕 f x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable hf
  have h4 : ∫ x, (𝓕 φ) x • (h2.toLp f) x = ∫ x, (𝓕 φ) x • f x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [h4, h3] at h1
  simpa [hφx] using h1
end GlobalTheory.GallagherLemma
