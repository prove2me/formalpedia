-- Prove2me | solution 1 for GlobalTheory.FormalConnection.T_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:59:33.731553+00:00
-- url     : https://prove2.me/submissions/dea87ff9-5bd8-45ed-a41d-147d84d70bc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Theorems.Thm_GlobalTheory_FormalConnection_ezF
import Theorems.Thm_GlobalTheory_FormalConnection_ez_y
import Theorems.Thm_GlobalTheory_FormalConnection_d_y
import Theorems.Thm_GlobalTheory_FormalConnection_d_F
import Theorems.Thm_GlobalTheory_FormalConnection_ez_Ar
import Theorems.Thm_GlobalTheory_FormalConnection_ez_dF
import Theorems.Thm_GlobalTheory_FormalConnection_C_cc_jac
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_cz1
import Theorems.Thm_GlobalTheory_FormalLog_ev_add
import Theorems.Thm_GlobalTheory_FormalLog_ev_mul
import Theorems.Thm_GlobalTheory_FormalLog_ev_sum
import Theorems.Thm_GlobalTheory_FormalLog_jac_F


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.FormalLog
open GlobalTheory GlobalTheory.FormalConnection
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace GlobalTheory.FormalConnection
theorem _root_.solution (b i j : Fin d) :
    ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G j i) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (Ar G j i)) +
      ∑ c, Jac G j c * C (constantCoeff (pderiv k ((0 : Fin 1), b) (Jac G c i))) := by
  have h := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) g)) (jac_F G j i)
  beta_reduce at h
  simp only [d_F, map_sum, ev_sum cz1, Derivation.leibniz, smul_eq_mul, ev_add cz1, ev_mul cz1, ezF, d_y, ez_y,
    ez_Ar, ez_dF, C_cc_jac, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  have hs : ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G j i) =
      ∑ c, pderiv k ((0 : Fin 1), c) (Jac G j i) * Jac G c b := Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hs, h, add_comm]
end GlobalTheory.FormalConnection
