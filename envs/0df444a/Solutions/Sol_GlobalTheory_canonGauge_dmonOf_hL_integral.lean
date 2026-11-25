-- Prove2me | solution 1 for GlobalTheory.canonGauge_dmonOf_hL_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:07.861739+00:00
-- url     : https://prove2.me/submissions/391307f1-d011-4439-a702-0fea1c27113a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_IP_gp
import Theorems.Thm_GlobalTheory_GaugeInt_int_C
import Theorems.Thm_GlobalTheory_GaugeInt_int_const
import Theorems.Thm_GlobalTheory_GaugeInt_di_of_exp
import Theorems.Thm_GlobalTheory_GaugeInt_dof_int
import Theorems.Thm_GlobalTheory_GaugeInt_quad_int
import Theorems.Thm_GlobalTheory_QuadDeriv_addOf_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_addOf
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_comp1
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_const_pderiv
import Theorems.Thm_GlobalTheory_QuadDeriv_constantCoeff_pderiv_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_unit_right
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_axes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_triple_points_zero_constant


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
open GlobalTheory
open GaugeInt
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
      [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h →
      ∀ (w0 : O) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
      (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
        ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
      ∀ m : ι →₀ ℕ, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) m
        (B.hL k h w0)) ∈ (algebraMap R k).range := by
  intro R _ d O _ _ k _ _ _ B g hg w0 ι _ u hβ m
  have iF : IP (algebraMap R k) (B.FK k) := ⟨B.G.F, B.G.const, rfl⟩
  have iw : IP (algebraMap R k) (B.actK k w0) := ⟨B.A.act w0, B.A.const w0, rfl⟩
  have hF := iF.gp
  have hw := iw.gp
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k w0) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k w0) (pt k (n := 2) d 0))
      (comp1 (B.actK k w0) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom w0)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const w0) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const w0) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have c0 : constantCoeff g = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 0 (by simp)
  have c1 : ∀ s, constantCoeff (pderiv k s g) = 0 := fun s => by
    rw [const_pderiv]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 _ (by simp)
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  have hl : DI (algebraMap R k) (defL (B.FK k) g) := by
    refine di_of_exp B.ph1 ?_ _ ?_ hg.ph1
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleLeft_zero_fst, map_one]
    · rw [defL, map_sub, map_add, gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (gp_addOf _ hF _ _ (hp _) (hp _)) (hp _)) _ c0]
      simp
  have hr : DI (algebraMap R k) (defR (B.FK k) g) := by
    refine di_of_exp B.ph2 ?_ _ ?_ hg.ph2
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleRight_zero_fst, map_one]
    · rw [defR, map_sub, map_add, gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (gp_addOf _ hF _ _ (hp _) (hp _))) _ c0]
      simp
  set U : ι → Fin d → k := fun l i => algebraMap R k (u l i) with hUdef
  have hu : ∀ l i, U l i ∈ (algebraMap R k).range := fun l i => ⟨u l i, rfl⟩
  have hq : B.hL k g w0 = ev (n := 1) ![pt k d 0, B.actK k w0] g := by
    rw [FB.hL, gt_comp1_pt_right]
  have h2 : ∀ l l', Dof (B.FK k) (U l) (Dof (B.FK k) (U l') (B.hL k g w0)) ∈
      IntS (algebraMap R k) 1 d := by
    intro l l'
    have h := add_mem (quad_int iF hU iw hom g c1 hl hr (hu l) (hu l'))
      (int_C (n := 1) (d := d) (add_mem (hβ l l') (hβ l' l)))
    rw [hq]
    convert h using 1
    rw [sub_add_eq_add_sub, eq_sub_iff_add_eq]
    congr 2
    simp only [dotProduct, Matrix.mulVec, bilinPart, dAct, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => by ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  let P : PS k 1 d → Prop := fun f => f = B.hL k g w0 ∨
    (∃ l, f = Dof (B.FK k) (U l) (B.hL k g w0)) ∨ f ∈ IntS (algebraMap R k) 1 d
  have hstep : ∀ l f, P f → P (Dof (B.FK k) (U l) f) := by
    rintro l f (rfl | ⟨l', rfl⟩ | hf)
    · exact Or.inr (Or.inl ⟨l, rfl⟩)
    · exact Or.inr (Or.inr (h2 l l'))
    · exact Or.inr (Or.inr (dof_int iF (hu l) hf))
  have hP : P (DmonOf (B.FK k) U m (B.hL k g w0)) := by
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => exact Or.inl rfl
    | cons a L ih => exact Function.Iterate.rec P ih (hstep a) (m a)
  rcases hP with e | ⟨l, e⟩ | e
  · rw [e, hq, gt_const_ev _ (pair_points_zero_constant (gp_pt 0) hw) _ c0]
    exact zero_mem _
  · rw [e, hq, Dof]
    simp only [map_sum, map_mul, constantCoeff_pderiv_formalSubst_two _ _ (gp_pt 0) hw, c1, zero_mul,
      Finset.sum_const_zero, add_zero, mul_zero]
    exact zero_mem _
  · exact int_const e
end GlobalTheory
