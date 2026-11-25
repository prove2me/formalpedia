-- Prove2me | solution 1 for GlobalTheory.FormalLog.cz_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:37.720809+00:00
-- url     : https://prove2.me/submissions/cb99fd3c-b3ed-42fc-9b56-3ec65aba7017

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution : ∀ i, constantCoeff (G.F i) = 0 := G.const
end GlobalTheory.FormalLog
