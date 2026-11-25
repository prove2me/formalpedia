-- Prove2me | solution 1 for GlobalTheory.GaugeSecondDeriv.ev_add_axis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:29.466434+00:00
-- url     : https://prove2.me/submissions/4adc966e-8e3c-4198-8238-53c07c12c886

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_cz12
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_zero__a29edcfaf6d8
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formalGroupLaw_ev_x_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
open GlobalTheory GlobalTheory.GaugeSecondDeriv
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.GaugeSecondDeriv
theorem _root_.solution (G : FGLaw k d) (c : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (G.F c)) =
      pt k (n := 2) d 1 c := by
  have h1 : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 1) CZ.nil
  have e := congrArg (ev (n := 2) ![pt k d 1]) (formalGroupLaw_ev_x_zero G c)
  rw [ev_ev h1 cz1, ev_X h1] at e
  rw [ev_ev czZ cz12]
  refine Eq.trans ?_ e
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ, ev_X h1, ev_zero' h1]
end GlobalTheory.GaugeSecondDeriv
