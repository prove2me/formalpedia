-- Prove2me | solution 1 for GlobalTheory.GaugeSecondDeriv.pderiv_ev_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:58.586943+00:00
-- url     : https://prove2.me/submissions/cfb1bf58-7a4b-42b1-8c65-259d2df1bc71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt


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
theorem _root_.solution (h : PS k 2 d) (q : Pt k 3 d) (hq : ∀ c, constantCoeff (q c) = 0) (b : Fin d) :
    pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, q] h) =
      ∑ j, ev (n := 3) ![pt k d 0, q] (pderiv k ((1 : Fin 2), j) h) * pderiv k ((2 : Fin 3), b) (q j) := by
  have hc : CZ (![pt k (n := 3) d 0, q] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons hq CZ.nil)
  rw [pderiv_ev hc, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pderiv_pt]
end GlobalTheory.GaugeSecondDeriv
