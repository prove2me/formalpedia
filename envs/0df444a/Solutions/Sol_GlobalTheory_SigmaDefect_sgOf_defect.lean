-- Prove2me | solution 1 for GlobalTheory.SigmaDefect.sgOf_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:26:13.007955+00:00
-- url     : https://prove2.me/submissions/3ac54fd9-9d39-49d8-984b-98b1be4e31f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Theorems.Thm_GlobalTheory_SigmaDefect_ev_sgOf
import Theorems.Thm_GlobalTheory_SigmaDefect_GP_FK
import Theorems.Thm_GlobalTheory_SigmaDefect_sigma_defect_eval_phase_one
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_formalExp
import Theorems.Thm_GlobalTheory_QuadDeriv_dz_right
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_GlobalTheory_QuadDeriv_hUp
import Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_vanish_first_axis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
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
open GlobalTheory GlobalTheory.SigmaDefect
open GlobalTheory.QuadDeriv GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace GlobalTheory.SigmaDefect
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (i : Fin d) :
    ev ![B.FK k] (sgOf k h i) = ev (n := 2) ![pt k d 0] (sgOf k h i) +
      ev (n := 2) ![pt k d 1] (sgOf k h i) +
      ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (FB.toK k B.ph1)) := by
  have hF := GP_FK (k := k) B
  have hp : ∀ j : Fin 2, GP (pt k d j) := gp_pt
  have h0 : constantCoeff h = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_vanish_first_axis h hc.ax0 0 fun _ => rfl
  have u0 : (pt k d 0 : Pt k 3 d) = up (pt k d 0) := (evP_pt _ (hUp (k := k) (d := d)) 0).symm
  have u1 : (pt k d 1 : Pt k 3 d) = up (pt k d 1) := (evP_pt _ (hUp (k := k) (d := d)) 1).symm
  have uF : addOf (B.FK k) (pt k d 0 : Pt k 3 d) (pt k d 1) = up (B.FK k) := rfl
  have hE : FB.toK k B.ph1 = GlobalTheory.FormalCalc.formalExp (ev ![up (pt k d 0), pt k d 2] h +
      ev ![up (pt k d 1), pt k d 2] h - ev ![up (B.FK k), pt k d 2] h) := by
    rw [← u0, ← u1, ← uF]; exact hc.ph1
  have c : ∀ a : Pt k 2 d, GP a → constantCoeff (ev ![up a, pt k d 2] h) = 0 := fun a ha =>
    gt_const_ev _ (pair_points_zero_constant (constantCoeff_up_eq_zero₂ ha) (gp_pt 2)) h h0
  have hD := GlobalTheory.FormalCalc.pderiv_formalExp (f := ev ![up (pt k d 0), pt k d 2] h +
      ev ![up (pt k d 1), pt k d 2] h - ev ![up (B.FK k), pt k d 2] h)
    (by rw [map_sub, map_add, c _ (hp 0), c _ (hp 1), c _ hF]; simp) ((2 : Fin 3), i)
  rw [← hE] at hD
  rw [hD, gt_ev_mul _ hDown, sigma_defect_eval_phase_one, one_mul, map_sub, map_add, gt_ev_sub _ hDown,
    gt_ev_add _ hDown, dz_right _ _ (hp 0), dz_right _ _ (hp 1), dz_right _ _ hF,
    ev_sgOf _ _ _ hF, ev_sgOf _ _ _ (hp 0), ev_sgOf _ _ _ (hp 1)]
  ring
end GlobalTheory.SigmaDefect
