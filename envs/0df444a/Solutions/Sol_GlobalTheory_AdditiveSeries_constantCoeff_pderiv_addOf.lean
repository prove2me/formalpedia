-- Prove2me | solution 1 for GlobalTheory.AdditiveSeries.constantCoeff_pderiv_addOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:43.509279+00:00
-- url     : https://prove2.me/submissions/422de2d2-4d01-41d0-984c-0211da2aed27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
import Theorems.Thm_GlobalTheory_AdditiveSeries_gp_cons
import Theorems.Thm_GlobalTheory_AdditiveSeries_pderiv_ev_cons
import Theorems.Thm_GlobalTheory_AdditiveSeries_ev_addOf
import Theorems.Thm_GlobalTheory_AdditiveSeries_addOf_zero
import Theorems.Thm_GlobalTheory_AdditiveSeries_pderiv_pt
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.AdditiveSeries
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.AdditiveSeries
theorem _root_.solution {q : ℕ} (G : FGLaw k d) (i l : Fin d) :
    constantCoeff (pderiv k ((0 : Fin (q + 2)), i)
      (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l)) = if l = i then 1 else 0 := by
  have hx : GP (pt k d (0 : Fin 1)) := gp_pt 0
  have hy : ∀ j, GP ((fun _ => 0 : Fin (q + 1) → Pt k 1 d) j) := fun _ => gp_zero₂
  have h := pderiv_ev_cons hx hy ((0 : Fin 1), i) (by simp)
    (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l)
  rw [ev_addOf (gp_cons hx hy)] at h
  have e1 : (Fin.cons (pt k d (0 : Fin 1)) (fun _ => 0) : Fin (q + 2) → Pt k 1 d) 1 = 0 := rfl
  rw [e1, Fin.cons_zero, addOf_zero G hx] at h
  simp only [pderiv_pt, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  rw [← gt_const_ev_eq _ (gp_cons hx hy), ← h]
  split_ifs <;> simp
end GlobalTheory.AdditiveSeries
