-- Prove2me | solution 1 for GlobalTheory.FormalLog.ev_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:52.408022+00:00
-- url     : https://prove2.me/submissions/d3d088c1-eeb4-44f9-a499-7cc535f3c08e

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
theorem _root_.solution (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by
  unfold ev pt
  exact congrFun subst_self f
end GlobalTheory.FormalLog
