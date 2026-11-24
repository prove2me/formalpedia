-- Prove2me | solution 1 for GlobalTheory.FormalLog.pderiv_second_ev_first_point_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:14.594849+00:00
-- url     : https://prove2.me/submissions/d070f4dd-d1ce-4d8a-8c64-0ec93145ca91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_czX
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev_zero
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_pt


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution (h : PS k 1 d) (b : Fin d) : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] h) = 0 :=
  pderiv_ev_zero czX _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
end GlobalTheory.FormalLog
