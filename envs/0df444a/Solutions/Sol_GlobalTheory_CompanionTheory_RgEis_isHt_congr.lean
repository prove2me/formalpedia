-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.isHt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:15.360659+00:00
-- url     : https://prove2.me/submissions/6eff59f3-5450-4f21-bfd7-9437e8cdc1a7

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
theorem _root_.solution {Γ K P : Subgroup G} {η θ : G → ℝ} (h : IsHt Γ K P η) (e : ∀ g, θ g = η g) : IsHt Γ K P θ := by
  rwa [show θ = η from funext e]
end GlobalTheory.CompanionTheory.RgEis
