-- Prove2me | solution 1 for GlobalTheory.FormalLog.logOf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:45:03.61562+00:00
-- url     : https://prove2.me/submissions/ee4ec1df-1689-400f-ba19-2a45f9f1d392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_d_evY
import Theorems.Thm_GlobalTheory_FormalLog_d_evX
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_first_ev_second_point_eq_zero
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_second_ev_first_point_eq_zero
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_logOf
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_cc_ev
import Theorems.Thm_GlobalTheory_FormalLog_constantCoeff_prim
import Theorems.Thm_GlobalTheory_FormalLog_czFF
import Theorems.Thm_GlobalTheory_FormalLog_czX
import Theorems.Thm_GlobalTheory_FormalLog_czY
import Theorems.Thm_GlobalTheory_FormalLog_d_evF
import Theorems.Thm_GlobalTheory_FormalLog_eq_C_of_pderiv_zero
import Theorems.Thm_GlobalTheory_FormalLog_om_P
import Theorems.Thm_GlobalTheory_FormalLog_om_Q


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
variable [Algebra ℚ k]
namespace GlobalTheory.FormalLog
theorem _root_.solution (i : Fin d) :
    ev (n := 2) ![G.F] (logOf G i) = ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i) := by
  rw [← sub_eq_zero]
  set g := ev (n := 2) ![G.F] (logOf G i) - (ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i))
  have hd : ∀ v, pderiv k v g = 0 := by
    rintro ⟨j, c⟩
    fin_cases j
    · simp only [Fin.zero_eta]
      simp only [g, map_sub, map_add, d_evF, pderiv_logOf, pderiv_first_ev_second_point_eq_zero, d_evX]
      rw [om_P G i c]; ring
    · simp only [Fin.mk_one]
      simp only [g, map_sub, map_add, d_evF, pderiv_logOf, pderiv_second_ev_first_point_eq_zero, d_evY]
      have := om_Q G i c
      simp only [Ar] at this
      rw [this]; ring
  have hc : constantCoeff g = 0 := by
    simp only [g, map_sub, map_add, cc_ev (czFF G), cc_ev czX, cc_ev czY, logOf, constantCoeff_prim]
    ring
  rw [eq_C_of_pderiv_zero hd, hc, map_zero]
end GlobalTheory.FormalLog
