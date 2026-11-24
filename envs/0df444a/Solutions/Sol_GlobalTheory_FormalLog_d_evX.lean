-- Prove2me | solution 1 for GlobalTheory.FormalLog.d_evX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:07:55.74287+00:00
-- url     : https://prove2.me/submissions/35df9b57-ff19-4a37-bcdf-e6ccedc5be7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_czX
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution (h : PS k 1 d) (a : Fin d) :
    pderiv k ((0 : Fin 2), a) (ev (n := 2) ![pt k d 0] h) = ev (n := 2) ![pt k d 0] (pderiv k ((0 : Fin 1), a) h) := by
  rw [pderiv_ev czX, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp [pderiv_pt]
end GlobalTheory.FormalLog
