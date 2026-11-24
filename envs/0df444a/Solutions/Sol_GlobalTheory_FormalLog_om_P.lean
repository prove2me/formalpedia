-- Prove2me | solution 1 for GlobalTheory.FormalLog.om_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:39:54.324936+00:00
-- url     : https://prove2.me/submissions/bbb7f1ba-04d9-40df-8e84-1c87343a72f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_om_Q
import Theorems.Thm_GlobalTheory_FormalLog_czSw
import Theorems.Thm_GlobalTheory_FormalLog_sw_F
import Theorems.Thm_GlobalTheory_FormalLog_sw_y
import Theorems.Thm_GlobalTheory_FormalLog_sw_dF
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_ev_mul
import Theorems.Thm_GlobalTheory_FormalLog_ev_sum


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
theorem _root_.solution (i a : Fin d) :
    ∑ j, ev (n := 2) ![G.F] (Om G i j) * pderiv k ((0 : Fin 2), a) (G.F j) = ev (n := 2) ![pt k d 0] (Om G i a) := by
  have h := congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) (om_Q G i a)
  rw [ev_sum czSw, sw_y] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul czSw, sw_F, Ar, sw_dF]
end GlobalTheory.FormalLog
