-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.isHt_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:11.313957+00:00
-- url     : https://prove2.me/submissions/3120c114-aebe-44f3-8a79-677e94aeac6d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G]
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {Γ K P : Subgroup G} {η θ : G → ℝ} (x y : ℝ) (h₁ : IsHt Γ K P η) (h₂ : IsHt Γ K P θ) :
    IsHt Γ K P fun g => x * η g + y * θ g where
  left p hp g := by simp only [h₁.left p hp g, h₂.left p hp g]; ring
  right g k hk := by simp only [h₁.right g k hk, h₂.right g k hk]
  rat γ hγ hp := by simp only [h₁.rat γ hγ hp, h₂.rat γ hγ hp]; ring
  cont := (continuous_const.mul h₁.cont).add (continuous_const.mul h₂.cont)
end GlobalTheory.CompanionTheory.RgEis
