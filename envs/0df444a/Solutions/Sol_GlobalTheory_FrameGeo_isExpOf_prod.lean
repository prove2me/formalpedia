-- Prove2me | solution 1 for GlobalTheory.FrameGeo.isExpOf_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:30:40.193113+00:00
-- url     : https://prove2.me/submissions/a734dfcb-5180-4b48-9ab4-2f9c9d885fee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_GlobalTheory_FrameGeo_IsExpOf_mul
import Theorems.Thm_GlobalTheory_FrameGeo_IsExpOf_one
import Theorems.Thm_GlobalTheory_FrameGeo_isExpOf_canonical_gauge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eq_zero_of_exp_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open GlobalTheory.FramePull ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {h : PS k 2 d}
namespace GlobalTheory.FrameGeo
theorem _root_.solution (hh : B.IsCanonGauge k h) (b c : O)
    (hQ : ev ![B.A.act b, B.A.act 0, B.A.act 0] B.ph2 = 1) (n : ℕ) :
    IsExpOf (∏ i ∈ Finset.range n, ev ![B.A.act b, B.A.act ((i : O) * c), B.A.act c] B.ph2)
      ((n : k) • ev ![B.actK k b, B.actK k c] h - ev ![B.actK k b, B.actK k ((n : O) * c)] h) := by
  induction n with
  | zero =>
    have h0 := isExpOf_canonical_gauge hh b 0 0
    rw [hQ, add_zero, add_sub_cancel_right] at h0
    have e : ev ![B.actK k b, B.actK k 0] h = 0 :=
      WickVanishing.eq_zero_of_exp_eq_one h0.1 (h0.2.symm.trans (map_one _))
    rw [Finset.prod_range_zero, Nat.cast_zero, Nat.cast_zero, zero_smul, zero_mul, e, sub_zero]
    exact IsExpOf.one
  | succ j ih =>
    have := ih.mul (isExpOf_canonical_gauge hh b ((j : O) * c) c)
    rw [Finset.prod_range_succ]
    convert this using 1
    rw [Nat.cast_succ, Nat.cast_succ, add_smul, one_smul, add_mul, _root_.one_mul]
    ring
end GlobalTheory.FrameGeo
