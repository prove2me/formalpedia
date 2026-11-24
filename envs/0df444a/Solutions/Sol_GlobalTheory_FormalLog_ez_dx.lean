-- Prove2me | solution 1 for GlobalTheory.FormalLog.ez_dx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:07:56.428045+00:00
-- url     : https://prove2.me/submissions/42ff9139-db9d-4e81-81bb-ac0f1706ef81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_cz1
import Theorems.Thm_GlobalTheory_FormalLog_formalGroupLaw_ev_x_zero
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
theorem _root_.solution (j a : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (G.F j)) = if j = a then 1 else 0 := by
  have h := congrArg (pderiv k ((0 : Fin 1), a)) (formalGroupLaw_ev_x_zero G j)
  rw [pderiv_ev cz1, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pderiv_pt] at h
  rw [h, pderiv_X]
  simp [Pi.single_apply]
end GlobalTheory.FormalLog
