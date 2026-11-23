-- Prove2me | solution 1 for GlobalTheory.FormalLog.cc_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:28.933197+00:00
-- url     : https://prove2.me/submissions/40fb1c80-917d-4d78-91fe-875322f1a399

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
namespace GlobalTheory.FormalLog
theorem _root_.solution {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt k n d) i) = 0 := by simp
end GlobalTheory.FormalLog
