-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.IsHt_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:58:53.413081+00:00
-- url     : https://prove2.me/submissions/ad9696c2-3bb5-47bf-94ea-381f5b92f62a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GalleryOfTubesAndCrossing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {Γ K P : Subgroup G} {η₁ η₂ η : G → ℝ} (h₁ : IsHt Γ K P η₁) (h₂ : IsHt Γ K P η₂)
    (s t : ℝ) (e : ∀ g, η g = s * η₁ g + t * η₂ g) : IsHt Γ K P η := by
  have he : η = fun g => s * η₁ g + t * η₂ g := funext e
  subst he
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hp => ?_, ?_⟩
  · simp only [h₁.left p hp g, h₂.left p hp g]; ring
  · simp only [h₁.right g k hk, h₂.right g k hk]
  · simp only [h₁.rat γ hγ hp, h₂.rat γ hγ hp]; ring
  · have c₁ := h₁.cont
    have c₂ := h₂.cont
    fun_prop
end GlobalTheory.CompanionTheory.RgEisGal
