-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Eis.tube_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:17.165749+00:00
-- url     : https://prove2.me/submissions/85a102b5-2aae-4179-9552-d4c7773a9b59

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdentityTubeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Eis
namespace GlobalTheory.CompanionTheory.Eis
theorem _root_.solution {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) :=
    (Complex.continuous_re.comp continuous_fst).prodMk (Complex.continuous_re.comp continuous_snd)
  exact hc.isOpen_preimage Ω hΩ
end GlobalTheory.CompanionTheory.Eis
