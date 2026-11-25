-- Prove2me | solution 1 for GlobalTheory.GaugeInt.dz_defR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:30.090821+00:00
-- url     : https://prove2.me/submissions/a4cc02d0-2343-4e76-b915-5ee1b6ba5f76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_IP_gp
import Theorems.Thm_GlobalTheory_GaugeInt_ip_pt
import Theorems.Thm_GlobalTheory_GaugeInt_ip_zero
import Theorems.Thm_GlobalTheory_GaugeInt_ip3
import Theorems.Thm_GlobalTheory_GaugeInt_int_ev
import Theorems.Thm_GlobalTheory_GaugeInt_ip_addOf
import Theorems.Thm_GlobalTheory_GaugeInt_ip_up
import Theorems.Thm_GlobalTheory_GaugeInt_di_ev
import Theorems.Thm_GlobalTheory_GaugeInt_ev_defR
import Theorems.Thm_GlobalTheory_QuadDeriv_dz_left
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_GlobalTheory_QuadDeriv_hUp
import Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv
open GlobalTheory GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
variable {φ}
namespace GlobalTheory.GaugeInt
theorem _root_.solution {F : Pt k 2 d} (hF : IP φ F) (g : PS k 2 d) (h : DI φ (defR F g))
    {a b : Pt k 2 d} (ha : IP φ a) (hb : IP φ b) (i : Fin d) :
    ev ![0, a] (pderiv k ((0 : Fin 2), i) g) + ev ![0, b] (pderiv k ((0 : Fin 2), i) g) -
      ev ![0, addOf F a b] (pderiv k ((0 : Fin 2), i) g) ∈ IntS φ 2 d := by
  have e : up (addOf F a b) = addOf F (up a) (up b) := evP_addOf _ hUp F _ _ ha.gp hb.gp
  rw [← dz_left g _ (ip_addOf hF ha hb).gp, ← dz_left g _ ha.gp, ← dz_left g _ hb.gp,
    ← gt_ev_add _ hDown, ← gt_ev_sub _ hDown, ← map_add, ← map_sub, e,
    ← ev_defR F hF.gp g _ _ _ (gp_pt 2) (constantCoeff_up_eq_zero₂ ha.gp) (constantCoeff_up_eq_zero₂ hb.gp)]
  exact int_ev (ip3 (ip_pt 0) (ip_pt 1) ip_zero) (di_ev (ip3 (ip_pt 2) (ip_up ha) (ip_up hb)) h _)
end GlobalTheory.GaugeInt
