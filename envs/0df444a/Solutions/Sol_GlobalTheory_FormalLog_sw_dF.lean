-- Prove2me | solution 1 for GlobalTheory.FormalLog.sw_dF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:51:55.998804+00:00
-- url     : https://prove2.me/submissions/ad2a5dff-0a46-4e8e-84e5-a262e74523c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_czSw
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution (j b : Fin d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), b) (G.F j)) = pderiv k ((0 : Fin 2), b) (G.F j) := by
  have h := congrArg (pderiv k ((0 : Fin 2), b)) (G.comm j)
  rw [pderiv_ev czSw, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pderiv_pt] at h
  exact h
end GlobalTheory.FormalLog
