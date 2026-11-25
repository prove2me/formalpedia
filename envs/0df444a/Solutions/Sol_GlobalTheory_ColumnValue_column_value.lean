-- Prove2me | solution 1 for GlobalTheory.ColumnValue.column_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:30:37.264865+00:00
-- url     : https://prove2.me/submissions/2412627a-0b75-449e-b825-00722fd61aa1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Theorems.Thm_GlobalTheory_ColumnValue_dmonOf_zero_index
import Theorems.Thm_GlobalTheory_ColumnValue_dmonOf_smul
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_PullbackColumn_dpolyOf_monomial_one
import Theorems.Thm_GlobalTheory_PullbackColumn_expS_pow
import Theorems.Thm_GlobalTheory_QuadDeriv_constantCoeff_mapP_eq_zero
import Theorems.Thm_GlobalTheory_canonGauge_dmonOf_hL_integral
import Theorems.Thm_GlobalTheory_constantCoeff_dmonOf_sub_mem
import Theorems.Thm_GlobalTheory_dmonOf_mul_expS_congr
import Theorems.Thm_GlobalTheory_invariantDeriv_along_endo
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_const_smul
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
open GlobalTheory GlobalTheory.ColumnValue
namespace GlobalTheory.ColumnValue
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (hh : B.IsCanonGauge k h)
    (w0 a : O) (N m : ℕ) (w : PS R 1 d)
    (hw : FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0))
    (I : Ideal R) {ι : Type} [Fintype ι] (u : ι → Fin d → R) (α : ι → R) (hI : ∀ l, α l ∈ I)
    (hα : ∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) =
      algebraMap R k (α l) • (fun i => algebraMap R k (u l i)))
    (hβ : ∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
      ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range)
    (f : PS R 1 d) (y : ι → R) (hf : ∀ l mo, coeff mo (Dof B.G.F (u l) f - C (y l) * f) ∈ I)
    (mo : ι →₀ ℕ) :
    ∃ s : R, s - (∏ l, y l ^ mo l) * constantCoeff f ∈ I ∧
      B.nabVal k h w0 (N * m) (FB.toK k (f * w ^ m)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w0) (gp_pt 0))) h hh0
  have cA : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0)) = 0 :=
    gt_const_ev _ (single_point_zero_constant (hA a)) _ cL
  have cD : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) = 0 := by
    rw [map_sub, cA, nt_const_smul, cL, mul_zero, sub_zero]
  have hG : FB.toK k (f * w ^ m) * FB.expS k (((N * m : ℕ) : k) • B.hL k h w0) =
      FB.toK k f * FB.expS k ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0)) := by
    have e : FB.toK k (f * w ^ m) = FB.toK k f * FB.toK k w ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hw, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      smul_sub, smul_smul, Nat.cast_mul, mul_comm (N : k) (m : k), sub_add_cancel]
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0))) = algebraMap R k r := by
    intro mo
    rcases eq_or_ne mo 0 with rfl | hmo
    · exact ⟨0, I.zero_mem, by rw [dmonOf_zero_index, nt_const_smul, cA, mul_zero, map_zero]⟩
    · obtain ⟨l, hl⟩ := Finsupp.ne_iff.1 hmo
      obtain ⟨t, ht⟩ := canonGauge_dmonOf_hL_integral R d O k B h hh w0 ι u hβ mo
      refine ⟨(m : R) * ((∏ l, α l ^ mo l) * t), I.mul_mem_left _ (I.mul_mem_right _
        (Ideal.prod_mem I (Finset.mem_univ l) (I.pow_mem_of_mem (hI l) _ (Nat.pos_of_ne_zero hl)))), ?_⟩
      rw [dmonOf_smul, map_mul, constantCoeff_C,
        (invariantDeriv_along_endo R d O k B a).2 ι _ (fun l => algebraMap R k (α l)) hα mo, ← ht]
      simp only [map_mul, map_prod, map_pow, map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cA, mul_zero]) hφ f mo
  refine ⟨constantCoeff (DmonOf B.G.F u mo f) + r, ?_, ?_⟩
  · rw [add_sub_right_comm]
    exact I.add_mem (constantCoeff_dmonOf_sub_mem R d B.G.F I ι u y f hf mo) hr
  · unfold FB.nabVal
    rw [hG, PullbackColumn.dpolyOf_monomial_one]
    exact e
end GlobalTheory.ColumnValue
