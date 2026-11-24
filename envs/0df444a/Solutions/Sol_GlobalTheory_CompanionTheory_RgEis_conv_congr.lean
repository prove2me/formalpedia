-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.conv_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:57:40.731802+00:00
-- url     : https://prove2.me/submissions/921f403b-7c14-4784-aa89-29365dfa7039

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
theorem _root_.solution {Γ P : Subgroup G} {l l' : G → ℝ} (h : Conv Γ P l) (e : ∀ g, l' g = l g) : Conv Γ P l' := by
  rwa [show l' = l from funext e]
end GlobalTheory.CompanionTheory.RgEis
