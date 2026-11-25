-- Prove2me | solution 1 for GlobalTheory.GaussWidths.all_widths_of_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:45.635357+00:00
-- url     : https://prove2.me/submissions/3f1982ca-a72b-4f57-903f-f8dc7d3f0c37

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
import Theorems.Thm_GlobalTheory_GaussWidths_hasWidth_all
import Theorems.Thm_GlobalTheory_GaussWidths_hasWidth_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussWidths
namespace GlobalTheory.GaussWidths
theorem _root_.solution
    (hconvAll : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
      ∀ (b c : ℝ), 0 < b → 0 < c →
      (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
      ∀ (h u : SchwartzMap E ℂ),
        (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
          Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
        u ∈ M) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro E _ _ _ _ _ M hM hℓ hF G hG hGM c hc g hg
  exact hasWidth_all (fun b c' hb hc' hP h u hu => hconvAll E M hM hℓ b c' hb hc' hP h u hu) hF
    (hasWidth_pi G hG hGM) c hc g hg
end GlobalTheory.GaussWidths
