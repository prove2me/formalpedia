-- Prove2me | solution 1 for GlobalTheory.FormalLog.ev_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:43.004698+00:00
-- url     : https://prove2.me/submissions/11efd17c-2369-4b36-b9d2-cd48ed2d2d1e

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
theorem _root_.solution {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : ev a (-f) = -ev a f := by
  simp only [← evHom_apply ha, map_neg]
end GlobalTheory.FormalLog
