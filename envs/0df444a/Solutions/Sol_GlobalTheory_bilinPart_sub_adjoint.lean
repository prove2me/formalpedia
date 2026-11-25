-- Prove2me | solution 1 for GlobalTheory.bilinPart_sub_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:48.499894+00:00
-- url     : https://prove2.me/submissions/c88437e5-b10f-42a4-8c0f-d8ca14fdf8dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeSubIsBiadd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Theorems.Thm_GlobalTheory_canonGauge_sub_isBiadd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ad_side1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ad_side2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_const_actK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace GlobalTheory
theorem _root_.solution (B : FB R d O) (h h' : PS k 2 d) (hh : B.IsCanonGauge k h)
    (hh' : B.IsCanonGauge k h') (a : O) :
    (dAct k B a).transpose * bilinPart k (h' - h) = bilinPart k (h' - h) * dAct k B (star a) := by
  have hp : ∀ {n : ℕ} (j : Fin n), WickVanishing.GP (pt k (n := n) d j) := fun j => WickVanishing.gp_pt j
  have hA : ∀ a, WickVanishing.GP (B.actK k a) := fun a i => WickVanishing.const_actK B a i
  have a1 := WickVanishing.pair_points_zero_constant (WickVanishing.gp_comp1 _ _ (hA a) (hp (n := 2) 0)) (hp 1)
  have a2 := WickVanishing.pair_points_zero_constant (hp (n := 2) 0) (WickVanishing.gp_comp1 _ _ (hA (star a)) (hp (n := 2) 1))
  have e := (canonGauge_sub_isBiadd R d O k B h h' hh hh').2.2.2.2 a
  rw [WickVanishing.gt_ev_sub _ a1, WickVanishing.gt_ev_sub _ a2] at e
  ext j i
  have e' := congrArg (coeff (Finsupp.single ((0 : Fin 2), j) 1 + Finsupp.single ((1 : Fin 2), i) 1)) e
  rw [map_sub, map_sub, WickVanishing.coeff_ad_side1 B h hh, WickVanishing.coeff_ad_side1 B h' hh', WickVanishing.coeff_ad_side2 B h hh,
    WickVanishing.coeff_ad_side2 B h' hh'] at e'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, bilinPart, map_sub, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  rw [← e']
  simp only [mul_comm]
end GlobalTheory
