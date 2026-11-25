-- Prove2me | solution 1 for GlobalTheory.GaugeSecondDeriv.ev_pderiv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:05:21.891157+00:00
-- url     : https://prove2.me/submissions/67158233-2f4e-49c4-8192-51d8f1bbf6df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_cz12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
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
theorem _root_.solution (F : PS k 2 d) (b : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] F)) =
      ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) F) := by
  rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
  have e : ((1 : Fin 3) = 2) = False := by simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_pt, Prod.mk.injEq, e, false_and,
    if_false, mul_zero, Finset.sum_const_zero, zero_add, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [ev_ev czZ cz12]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ]
end GlobalTheory.GaugeSecondDeriv
