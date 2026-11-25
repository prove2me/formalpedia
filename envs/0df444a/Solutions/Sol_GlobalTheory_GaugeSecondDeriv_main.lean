-- Prove2me | solution 1 for GlobalTheory.GaugeSecondDeriv.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:18:38.558283+00:00
-- url     : https://prove2.me/submissions/718f27a3-a1cf-4bcb-87ca-38d0e7ea00d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_cz12
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_pderiv_ev_second
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_ev_pderiv_add
import Theorems.Thm_GlobalTheory_GaugeSecondDeriv_ev_add_axis
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_constantCoeff_second_factor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_dlog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_integral_family_pair_zero


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
theorem _root_.solution : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ b : Fin d, ∃ K : PS R 2 d, ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) * pderiv k ((1 : Fin 2), j) h =
    FB.toK k K + ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h)) := by
  intro R _ d O _ _ k _ _ _ B h hc b
  have hA : ∀ c, constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) c) = 0 :=
    fun c => constantCoeff_ev cz12 ((lawK k B).const c)
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2)] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h) = 0 := by
    rw [map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph2 (constantCoeff_second_factor B) _ hH0 hc.ph2 ((2 : Fin 3), b)
  have h2 := ig_ev czZ integral_family_pair_zero hH
  have t1 : pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] h) = 0 :=
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have t2 : ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 2] h)) =
      ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h) := by
    rw [pderiv_ev_second h _ (cc_pt 2)]
    simp only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ev_ev czZ c02]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  have t3 : ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b)
      (ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)) =
      ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) *
        pderiv k ((1 : Fin 2), j) h := by
    rw [pderiv_ev_second h _ hA, ev_sum czZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun i c => ev (n := 2) ![pt k d 0, pt k d 1, 0]
        ((![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2)] : Fin 2 → Pt k 3 d) i c)) =
        fun i => pt k (n := 2) d i := by
      funext i c
      fin_cases i
      · simp [pt_apply, ev_X czZ]
      · exact ev_add_axis (lawK k B) c
    rw [ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]
    congr 1
    exact ev_pderiv_add (B.FK k j) b
  rw [map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3] at h2
  obtain ⟨K, hK⟩ := RingHom.mem_range.1 h2
  refine ⟨-K, ?_⟩
  rw [FB.toK, map_neg, hK]
  ring
end GlobalTheory.GaugeSecondDeriv
