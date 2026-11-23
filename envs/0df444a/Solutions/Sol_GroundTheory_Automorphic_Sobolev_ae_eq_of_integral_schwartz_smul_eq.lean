-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.ae_eq_of_integral_schwartz_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:33.335086+00:00
-- url     : https://prove2.me/submissions/520926d8-2e27-4cf1-8ff1-f81d35dd1131

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {m : E → ℂ} {C s t : ℝ}
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {g₁ g₂ : E → F}
    (h₁ : LocallyIntegrable g₁ (volume : Measure E)) (h₂ : LocallyIntegrable g₂ (volume : Measure E))
    (h : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → ∫ x, φ x • g₁ x = ∫ x, φ x • g₂ x) :
    g₁ =ᵐ[volume] g₂ := by
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero (h₁.sub h₂) fun g g_smooth g_cpt ↦ by
    have hc₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hc₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    set φ := hc₁.toSchwartzMap hc₂
    have hφ : ∀ x, φ x = (g x : ℂ) := fun x ↦ rfl
    have hφc : HasCompactSupport φ := hc₁
    have i₁ : Integrable (fun x ↦ φ x • g₁ x) (volume : Measure E) :=
      h₁.integrable_smul_left_of_hasCompactSupport φ.continuous hφc
    have i₂ : Integrable (fun x ↦ φ x • g₂ x) (volume : Measure E) :=
      h₂.integrable_smul_left_of_hasCompactSupport φ.continuous hφc
    have e : ∀ x, g x • (g₁ - g₂) x = φ x • g₁ x - φ x • g₂ x := fun x ↦ by
      rw [hφ, Pi.sub_apply, smul_sub, Complex.coe_smul, Complex.coe_smul]
    simp_rw [e]
    rw [integral_sub i₁ i₂, h φ hφc, sub_self]
  filter_upwards [this] with x hx
  exact sub_eq_zero.1 hx
end GroundTheory.Automorphic.Sobolev
