-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.dz_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:36.542802+00:00
-- url     : https://prove2.me/submissions/d14a0c19-8358-4968-9868-ed7ff26d4c2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_add_left
import Theorems.Thm_GlobalTheory_QuadDeriv_hUp
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
import Theorems.Thm_GlobalTheory_QuadDeriv_dz_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add


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
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) (hF : GP F) (g : PS k 2 d)
include hF
namespace GlobalTheory.QuadDeriv
theorem _root_.solution
    (h : ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g)
    (a b : Pt k 2 d) (ha : GP a) (hb : GP b) (i : Fin d) :
    ev ![addOf F a b, 0] (pderiv k ((1 : Fin 2), i) g) =
      ev ![a, 0] (pderiv k ((1 : Fin 2), i) g) + ev ![b, 0] (pderiv k ((1 : Fin 2), i) g) := by
  rw [← dz_right g _ (gp_addOf F hF _ _ ha hb), ← dz_right g _ ha, ← dz_right g _ hb,
    ← gt_ev_add _ hDown, ← map_add, ← add_left F hF g h _ _ _ (constantCoeff_up_eq_zero₂ ha) (constantCoeff_up_eq_zero₂ hb) (gp_pt 2)]
  unfold up
  rw [evP_addOf _ hUp F _ _ ha hb]
end GlobalTheory.QuadDeriv
