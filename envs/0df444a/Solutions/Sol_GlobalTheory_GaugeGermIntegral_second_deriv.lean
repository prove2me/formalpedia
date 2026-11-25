-- Prove2me | solution 1 for GlobalTheory.GaugeGermIntegral.second_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:40.781005+00:00
-- url     : https://prove2.me/submissions/03dd733a-78b3-433a-a87d-70b3a52b6466

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_map_self
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_FK_self
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_cz12
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_ev_add_axis
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_ev_pderiv_add
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_pderiv_ev_second
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_sum
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz01
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_pderiv_expS
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
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
  ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
open GlobalTheory GlobalTheory.GaugeGermIntegral
variable {K : Type} [Field K]
variable [CharZero K] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
open GlobalTheory.GaugeSecondDeriv
namespace GlobalTheory.GaugeGermIntegral
theorem _root_.solution (B : FB K d O) (h : PS K 2 d) (hc : B.IsCanonGauge K h) (b : Fin d) :
    ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) -
        ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b) B.ph2) := by
  have hA : ∀ c, constantCoeff (addOf B.G.F (pt K (n := 3) d 1) (pt K d 2) c) = 0 :=
    fun c => constantCoeff_ev LogPf.cz12 (B.G.const c)
  have c02 : CZ (![pt K (n := 3) d 0, pt K d 2] : Fin 2 → Pt K 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] :
      Fin 2 → Pt K 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt K d 0, pt K d 1] h +
      ev (n := 3) ![pt K d 0, pt K d 2] h -
      ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h) = 0 := by
    rw [map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]
    simp
  have hE := hc.ph2
  rw [FB.toK, map_self, FK_self] at hE
  have hH := pderiv_expS hH0 ((2 : Fin 3), b)
  rw [← hE] at hH
  have t1 : pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 1] h) = 0 :=
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have t2 : ev (n := 2) ![pt K d 0, pt K d 1, 0]
      (pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 2] h)) =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) := by
    rw [pderiv_ev_second h _ (cc_pt 2)]
    simp only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ev_ev czZ c02]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  have t3 : ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b)
      (ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h)) =
      ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h := by
    rw [pderiv_ev_second h _ hA, ev_sum czZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun i c => ev (n := 2) ![pt K d 0, pt K d 1, 0]
        ((![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] :
          Fin 2 → Pt K 3 d) i c)) = fun i => pt K (n := 2) d i := by
      funext i c
      fin_cases i
      · simp [pt_apply, ev_X czZ]
      · exact ev_add_axis B.G c
    rw [ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]
    congr 1
    exact ev_pderiv_add (B.G.F j) b
  rw [hH, ev_mul czZ, B.cocycleRight_zero_thd, one_mul, map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3]
  ring
end GlobalTheory.GaugeGermIntegral
