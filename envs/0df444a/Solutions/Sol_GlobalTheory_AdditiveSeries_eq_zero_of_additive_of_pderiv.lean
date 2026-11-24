-- Prove2me | solution 1 for GlobalTheory.AdditiveSeries.eq_zero_of_additive_of_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:20:48.952028+00:00
-- url     : https://prove2.me/submissions/e1ab314d-c71c-49d4-bcab-b4b4d9159a69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
import Theorems.Thm_GlobalTheory_AdditiveSeries_gp_cons
import Theorems.Thm_GlobalTheory_AdditiveSeries_ev_pt
import Theorems.Thm_GlobalTheory_AdditiveSeries_pderiv_ev_cons
import Theorems.Thm_GlobalTheory_AdditiveSeries_ev_ev_cons
import Theorems.Thm_GlobalTheory_AdditiveSeries_ev_pt_apply
import Theorems.Thm_GlobalTheory_AdditiveSeries_ev_addOf
import Theorems.Thm_GlobalTheory_AdditiveSeries_zero_addOf
import Theorems.Thm_GlobalTheory_AdditiveSeries_pderiv_pt
import Theorems.Thm_GlobalTheory_AdditiveSeries_constantCoeff_pderiv_addOf
import Theorems.Thm_GlobalTheory_FormalCalc_ext_of_pderiv_of_subst
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst
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
theorem _root_.solution (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ)
    (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d)
    (hadd : ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1))
        (fun j : Fin q => pt k d j.succ.succ)) g =
      ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g +
      ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g)
    (hlin : ∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j))
      (pderiv k ((0 : Fin (q + 1)), i) g) = 0) : g = 0 := by
  have : IsAddTorsionFree k := .of_module_rat k
  have hS : GP (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1)) :=
    gp_addOf _ G.const _ _ (gp_pt _) (gp_pt _)
  have hw : ∀ j : Fin q, GP (pt k d j.succ.succ) := fun _ => gp_pt _
  set V : Fin (q + 2) → Pt k (q + 1) d := Fin.cons 0 fun j => pt k d j with hVdef
  have hV : ∀ j, GP (V j) := gp_cons gp_zero₂ fun _ => gp_pt _
  have hV0 : V 0 = 0 := rfl
  have hV1 : V 1 = pt k d 0 := rfl
  have hVs : ∀ j : Fin q, V j.succ.succ = pt k d j.succ := fun _ => rfl
  have hid : (Fin.cons (pt k d 0) fun j : Fin q => pt k d j.succ :
      Fin (q + 1) → Pt k (q + 1) d) = fun j => pt k d j := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

  have eS (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1))
      (fun j : Fin q => pt k d j.succ.succ)) f) = f := by
    rw [ev_ev_cons hV hS hw]
    simp only [ev_addOf hV, ev_pt_apply hV, hV0, hV1, hVs, zero_addOf G (gp_pt _)]
    exact (congrArg (ev · f) hid).trans (ev_pt f)
  have e0 (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (pt k d 0)
      (fun j : Fin q => pt k d j.succ.succ)) f) =
      ev (Fin.cons 0 fun j : Fin q => pt k d j.succ) f := by
    rw [ev_ev_cons hV (gp_pt _) hw]
    simp only [ev_pt_apply hV, hV0, hVs]
  have e1 (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (pt k d 1)
      (fun j : Fin q => pt k d j.succ.succ)) f) = f := by
    rw [ev_ev_cons hV (gp_pt _) hw]
    simp only [ev_pt_apply hV, hV1, hVs]
    exact (congrArg (ev · f) hid).trans (ev_pt f)
  have hlin' (i : Fin d) : ev (Fin.cons 0 fun j : Fin q => pt k d j.succ)
      (pderiv k ((0 : Fin (q + 1)), i) g) = 0 := by
    have hU : ∀ j : Fin q, GP (pt k d j.succ) := fun _ => gp_pt _
    have h := congrArg (ev fun j : Fin q => pt k d j.succ) (hlin i)
    rw [ev_ev_cons hU gp_zero₂ (fun _ => gp_pt _), gt_ev_zero _ hU] at h
    simp only [ev_pt_apply hU, Pi.zero_apply, gt_ev_zero _ hU] at h
    exact h
  have hax : ev (Fin.cons 0 fun j : Fin q => pt k d j.succ) g = 0 := by
    have h := congrArg (ev V) hadd
    rw [gt_ev_add V hV, eS, e0, e1] at h
    simpa using h
  let J : Matrix (Fin d) (Fin d) (PS k (q + 1) d) := Matrix.of fun l i =>
    ev V (pderiv k ((0 : Fin (q + 2)), i) (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l))
  have hJ : IsUnit J := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det]
    have : (constantCoeff : PS k (q + 1) d →+* k).mapMatrix J = 1 := by
      ext l i
      simp [J, gt_const_ev_eq V hV, constantCoeff_pderiv_addOf, Matrix.one_apply]
    rw [this, Matrix.det_one]
    exact isUnit_one
  have hD : Matrix.vecMul (fun l => pderiv k ((0 : Fin (q + 1)), l) g) J = 0 := by
    funext i
    have hv : ∀ (j : Fin q) (l : Fin d),
        pderiv k ((0 : Fin (q + 2)), i) (pt k d j.succ.succ l) = 0 := by
      intro j l
      rw [pderiv_pt, if_neg fun h => Fin.succ_ne_zero _ h.1]
    have h := congrArg (pderiv k ((0 : Fin (q + 2)), i)) hadd
    rw [map_add, pderiv_ev_cons hS hw _ hv, pderiv_ev_cons (gp_pt _) hw _ hv,
      pderiv_ev_cons (gp_pt _) hw _ hv] at h
    simp only [pderiv_pt, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, one_ne_zero, false_and, if_false, Finset.sum_const_zero,
      add_zero] at h
    have h2 := congrArg (ev V) h
    rw [e0, hlin'] at h2
    have hs : ∀ f : Fin d → PS k (q + 2) d, ev V (∑ l, f l) = ∑ l, ev V (f l) := fun f => by
      unfold ev
      rw [← coe_substAlgHom (gt_hasSubst V hV), map_sum]
    simp only [hs, gt_ev_mul V hV, eS] at h2
    exact h2
  have hD0 : (fun l => pderiv k ((0 : Fin (q + 1)), l) g) = 0 := by
    obtain ⟨u, hu⟩ := hJ.exists_right_inv
    have h := congrArg (fun v => Matrix.vecMul v u) hD
    simpa [Matrix.vecMul_vecMul, hu] using h
  refine FormalCalc.ext_of_pderiv_of_subst (fun i : Fin d => ((0 : Fin (q + 1)), i))
    (b := fun p : Fin (q + 1) × Fin d =>
      (Fin.cons 0 fun j : Fin q => pt k d j.succ : Fin (q + 1) → Pt k (q + 1) d) p.1 p.2)
    (fun _ => rfl) ?_ (fun i => ?_) ?_
  · rintro ⟨j, i⟩ hj
    revert hj
    refine Fin.cases (fun hj => ?_) (fun j _ => rfl) j
    exact absurd ⟨i, rfl⟩ hj
  · simpa using congrFun hD0 i
  · exact hax.trans (gt_ev_zero _ (gp_cons gp_zero₂ fun _ => gp_pt _)).symm
end GlobalTheory.AdditiveSeries
