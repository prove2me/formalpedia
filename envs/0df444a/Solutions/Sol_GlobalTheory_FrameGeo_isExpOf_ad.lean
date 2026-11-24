-- Prove2me | solution 1 for GlobalTheory.FrameGeo.isExpOf_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:46.482158+00:00
-- url     : https://prove2.me/submissions/ba8c0e61-fbc1-4f1d-b8e0-8957b1ef69d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_GlobalTheory_FrameGeo_isExpOf_ev
import Theorems.Thm_GlobalTheory_FramePull_actK_mul
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_actK
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_comp1
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_ev_eq
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_point
import Theorems.Thm_GlobalTheory_FramePull_cz2
import Theorems.Thm_GlobalTheory_FramePull_ev_comp1
import Theorems.Thm_GlobalTheory_FramePull_ev_minus
import Theorems.Thm_GlobalTheory_FramePull_ev_point_fun
import Theorems.Thm_GlobalTheory_FramePull_germEv_germEv_two_points


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
theorem _root_.solution (hh : B.IsCanonGauge k h) (a b c : O) :
    IsExpOf (ev ![B.A.act b, B.A.act c] (B.ad a))
      (ev ![B.actK k (a * b), B.actK k c] h - ev ![B.actK k b, B.actK k (star a * c)] h) := by
  have p0 : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt k d j i) = 0 := constantCoeff_point
  have c0 : ∀ (e : O) (j : Fin 2) (i : Fin d), constantCoeff (comp1 (B.actK k e) (pt k d j) i) = 0 :=
    fun e j => constantCoeff_comp1 (constantCoeff_actK B e) (p0 j)
  have key := isExpOf_ev (cz2 (B.A.const b) (B.A.const c)) (by
    rw [map_sub, constantCoeff_ev_eq (cz2 (c0 a 0) (p0 1)), constantCoeff_ev_eq (cz2 (p0 0) (c0 _ 1)),
      sub_self]) (hh.ad a)
  have e : (fun j i => FB.toK k ((![B.A.act b, B.A.act c] : Fin 2 → Pt R 1 d) j i)) =
      ![B.actK k b, B.actK k c] := by
    funext j; fin_cases j <;> rfl
  have hb := cz2 (constantCoeff_actK (k := k) B b) (constantCoeff_actK (k := k) B c)
  rw [e, ev_minus hb, germEv_germEv_two_points (c0 a 0) (p0 1) hb, germEv_germEv_two_points (p0 0) (c0 _ 1) hb, ev_comp1 _ (p0 0) hb,
    ev_comp1 _ (p0 1) hb, ev_point_fun hb, ev_point_fun hb] at key
  rw [actK_mul, actK_mul]
  exact key
end GlobalTheory.FrameGeo
