-- Prove2me | solution 1 for GlobalTheory.FormalLog.ez_dy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:44.096042+00:00
-- url     : https://prove2.me/submissions/080a0c4b-c115-485d-9ace-2790212e6e7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
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
theorem _root_.solution (c b : Fin d) : ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F c)) = Jac G c b := rfl
end GlobalTheory.FormalLog
