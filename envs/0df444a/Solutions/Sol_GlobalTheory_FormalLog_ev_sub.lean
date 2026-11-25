-- Prove2me | solution 1 for GlobalTheory.FormalLog.ev_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:47.932077+00:00
-- url     : https://prove2.me/submissions/54971a35-e333-46e4-960c-eb4d0d2a1b57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_FormalLog_evHom_apply

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
variable {k : Type} [CommRing k] {d m n : ℕ}
namespace GlobalTheory.FormalLog
theorem _root_.solution {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f - g) = ev a f - ev a g := by
  simp only [← evHom_apply ha, map_sub]
end GlobalTheory.FormalLog
