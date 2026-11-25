-- Prove2me | solution 1 for GlobalTheory.exists_integral_germ_nabVal_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:14:37.292287+00:00
-- url     : https://prove2.me/submissions/bf67c9f5-c3cf-4264-a97b-11123e7ca77e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralGermNabValCongr
import Theorems.Thm_GlobalTheory_IntegralColumnGerm_prod_pow_sub_one_mem
import Theorems.Thm_GlobalTheory_IntegralColumnGerm_exists_eq_of_unit_mul
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FramePull_ev_actK_hL
import Theorems.Thm_GlobalTheory_FramePull_expIntegral_ad
import Theorems.Thm_GlobalTheory_FramePull_hL_eq
import Theorems.Thm_GlobalTheory_PullbackColumn_dpolyOf_monomial_one
import Theorems.Thm_GlobalTheory_PullbackColumn_expS_pow
import Theorems.Thm_GlobalTheory_QuadDeriv_constantCoeff_mapP_eq_zero
import Theorems.Thm_GlobalTheory_QuadDeriv_map_ev
import Theorems.Thm_GlobalTheory_dmonOf_mul_expS_congr
import Theorems.Thm_GlobalTheory_invariantDeriv_along_endo
import Theorems.Thm_GlobalTheory_map_dmonOf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dmonOf_Cmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_const_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_ev_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
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
open GlobalTheory
open IntegralColumnGerm
namespace GlobalTheory
theorem _root_.solution :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w : O) (N : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ mo : ι →₀ ℕ, ∃ r : R, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (B.hL k h ((N : O) * w))) = algebraMap R k (N * r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) := by
  intro hS hL R _ d O _ _ k _ _ _ B h hh hinj w0 a c N m I hac hN ι _ u α hα1 hαu hα hβ χ
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : ∀ w : O, constantCoeff (B.hL k h w) = 0 := fun w =>
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w) (gp_pt 0))) h hh0
  have e0 : star a * (w0 * a) = (N : O) * (c * w0) := by linear_combination w0 * hac
  have h1 := FramePull.expIntegral_ad hh a 1 (w0 * a)
  rw [e0, mul_one, ← FramePull.ev_actK_hL, ← FramePull.hL_eq] at h1
  obtain ⟨cD, υ, υ1, hυ⟩ := h1
  have hinv : υ * invOfUnit υ 1 = 1 := mul_invOfUnit υ 1 (by simpa using υ1)
  obtain ⟨g, hg⟩ : ∃ g : PS R 1 d, g * υ ^ m = χ :=
    ⟨χ * invOfUnit υ 1 ^ m, by rw [mul_assoc, ← mul_pow, mul_comm _ υ, hinv, one_pow, mul_one]⟩
  refine ⟨g, fun mo => ?_⟩
  have hga : FB.toK k (ev (n := 1) ![B.A.act a] g) = ev (n := 1) ![B.actK k a] (FB.toK k g) := by
    rw [FB.toK, QuadDeriv.map_ev _ _ (single_point_zero_constant (B.A.const a))]
    congr 1
    funext j; fin_cases j; rfl
  have hG : ev (n := 1) ![B.actK k a] (FB.toK k g * FB.expS k ((m : k) • B.hL k h w0)) =
      FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) *
        FB.expS k ((m : k) • B.hL k h ((N : O) * (c * w0))) := by
    have e : FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) =
        FB.toK k (ev (n := 1) ![B.A.act a] g) * FB.toK k υ ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hga, hυ, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      gt_ev_mul _ (single_point_zero_constant (hA a)),
      gt_ev_expS _ (single_point_zero_constant (hA a)) _ (by rw [nt_const_smul, cL, mul_zero]), nt_ev_smul _ (single_point_zero_constant (hA a)),
      smul_sub, sub_add_cancel]
  have hend := (invariantDeriv_along_endo R d O k B a).2 ι (fun l i => algebraMap R k (u l i))
    (fun l => algebraMap R k (α l)) hα
  have hmap : ∀ (mo : ι →₀ ℕ) (f : PS R 1 d),
      constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (FB.toK k f)) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo f)) := fun mo f => by
    rw [← constantCoeff_map, map_dmonOf]
    rfl
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • B.hL k h ((N : O) * (c * w0)))) = algebraMap R k r := by
    intro mo
    obtain ⟨t, ht⟩ := hS R d O k B h hh (c * w0) N ι u hβ mo
    refine ⟨(m : R) * (N * t), I.mul_mem_left _ (I.mul_mem_right _ hN), ?_⟩
    rw [smul_eq_C_mul, GE.dmonOf_Cmul, map_mul, constantCoeff_C, ht, map_mul (algebraMap R k) (m : R),
      map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cL, mul_zero]) hφ (ev (n := 1) ![B.A.act a] g * υ ^ m) mo
  have hcong : ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) -
      constantCoeff (DmonOf B.G.F u mo g) ∈ I := by
    intro mo
    have e1 : constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) =
        (∏ l, α l ^ mo l) * constantCoeff (DmonOf B.G.F u mo g) := by
      apply hinj
      rw [← hmap, hga, hend, hmap]
      simp only [map_mul, map_prod, map_pow]
    rw [e1, ← sub_one_mul]
    exact I.mul_mem_right _ (prod_pow_sub_one_mem I α hα1 mo)
  have hleib := hL R d B.G.F I ι u _ _ (υ ^ m) hcong mo
  rw [hg] at hleib
  refine exists_eq_of_unit_mul (algebraMap R k) I (P := ∏ l, α l ^ mo l)
    (x := constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g * υ ^ m)) + r)
    (IsUnit.prod_univ_iff.2 fun l => (hαu l).pow _) (prod_pow_sub_one_mem I α hα1 mo) ?_ ?_
  · rw [add_sub_right_comm]
    exact I.add_mem hleib hr
  · unfold FB.nabVal
    rw [PullbackColumn.dpolyOf_monomial_one, ← e]
    simp only [map_prod, map_pow]
    rw [← hend, hG]
    rfl
end GlobalTheory
