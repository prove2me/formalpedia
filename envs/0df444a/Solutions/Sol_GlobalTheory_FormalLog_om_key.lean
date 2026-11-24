-- Prove2me | solution 1 for GlobalTheory.FormalLog.om_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:30.597919+00:00
-- url     : https://prove2.me/submissions/a75e0a78-f888-4cd9-8b80-87310a7b70a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_om_Q
import Theorems.Thm_GlobalTheory_FormalLog_czX
import Theorems.Thm_GlobalTheory_FormalLog_om_P
import Theorems.Thm_GlobalTheory_FormalLog_d_evF
import Theorems.Thm_GlobalTheory_FormalLog_ez_F
import Theorems.Thm_GlobalTheory_FormalLog_ez_dx
import Theorems.Thm_GlobalTheory_FormalLog_ez_dy
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_comm
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_cz1
import Theorems.Thm_GlobalTheory_FormalLog_czY
import Theorems.Thm_GlobalTheory_FormalLog_ev_add
import Theorems.Thm_GlobalTheory_FormalLog_ev_mul
import Theorems.Thm_GlobalTheory_FormalLog_ev_sum
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_comm
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev_zero
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_pt
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
theorem _root_.solution (i a b : Fin d) :
    ∑ j, Jac G j b * pderiv k ((0 : Fin 1), a) (Om G i j) = ∑ c, pderiv k ((0 : Fin 1), c) (Om G i a) * Jac G c b := by
  have hQ := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) g)) (om_Q G i b)
  have hP := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) g)) (om_P G i a)
  beta_reduce at hQ hP
  rw [pderiv_ev_zero czY _ _ (fun j l => by fin_cases j; simp [pderiv_pt]), ev_zero' cz1] at hQ
  rw [pderiv_ev_zero czX _ _ (fun j l => by fin_cases j; simp [pderiv_pt]), ev_zero' cz1] at hP
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, d_evF, ev_sum cz1, ev_add cz1, ev_mul cz1, ez_F, ez_dx,
    ez_dy, Ar, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hQ hP
  rw [Finset.sum_add_distrib] at hQ hP
  have hR : ∑ j, Om G i j * ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (pderiv k ((1 : Fin 2), b) (G.F j))) =
      ∑ j, Om G i j * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (pderiv k ((0 : Fin 2), a) (G.F j))) := by
    simp only [pderiv_comm ((0 : Fin 2), a) ((1 : Fin 2), b)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, one_mul, zero_mul] at hQ hP
  rw [hR] at hQ
  linear_combination hQ - hP
end GlobalTheory.FormalLog
