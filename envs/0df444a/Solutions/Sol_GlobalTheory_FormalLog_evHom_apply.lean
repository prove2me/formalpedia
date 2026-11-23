-- Prove2me | solution 1 for GlobalTheory.FormalLog.evHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:58.47846+00:00
-- url     : https://prove2.me/submissions/9c837607-e5fe-49e1-a480-d2611c0ff9d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv

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
theorem _root_.solution {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : evHom ha f = ev a f := by
  simp [evHom, ev]
end GlobalTheory.FormalLog
