-- Prove2me | solution 1 for GlobalTheory.FormalLog.czY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:56.128687+00:00
-- url     : https://prove2.me/submissions/19c7feab-a8e6-464f-aaa6-b76944e306ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Theorems.Thm_GlobalTheory_FormalLog_cc_pt
import Theorems.Thm_GlobalTheory_FormalLog_CZ_nil
import Theorems.Thm_GlobalTheory_FormalLog_CZ_cons
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt


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
theorem _root_.solution : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 1) CZ.nil
end GlobalTheory.FormalLog
