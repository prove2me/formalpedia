-- Prove2me | solution 1 for GlobalTheory.FormalLog.formal_ev_second_point_of_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:59.213798+00:00
-- url     : https://prove2.me/submissions/dd82a00f-9044-42ce-9578-e4a2c39d0404

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Theorems.Thm_GlobalTheory_FormalLog_pt_apply
import Theorems.Thm_GlobalTheory_FormalLog_cz1
import Theorems.Thm_GlobalTheory_FormalLog_czY
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_ev_X
import Theorems.Thm_GlobalTheory_FormalLog_ev_ev
import Theorems.Thm_P2M_GlobalTheory_FormalLog_ev_zero__96b7e70e62c8


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
theorem _root_.solution (g : PS k 2 d) :
    ev (n := 2) ![pt k d 1] (ev (n := 1) ![pt k d 0, 0] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czY cz1]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czY, ev_zero' czY]
end GlobalTheory.FormalLog
