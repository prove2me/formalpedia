-- Prove2me | solution 1 for GlobalTheory.FrameGeo.isExpOf_canonical_gauge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:27:54.009375+00:00
-- url     : https://prove2.me/submissions/b11979aa-2e99-437e-991d-195fa776c7c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_GlobalTheory_FrameGeo_isExpOf_ev
import Theorems.Thm_GlobalTheory_FramePull_actK_add
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_FK
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_actK
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_addOf
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_ev_eq
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_point
import Theorems.Thm_GlobalTheory_FramePull_cz2
import Theorems.Thm_GlobalTheory_FramePull_cz3
import Theorems.Thm_GlobalTheory_FramePull_ev_addOf
import Theorems.Thm_GlobalTheory_FramePull_ev_minus
import Theorems.Thm_GlobalTheory_FramePull_ev_plus
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
theorem _root_.solution (hh : B.IsCanonGauge k h) (b c c' : O) :
    IsExpOf (ev ![B.A.act b, B.A.act c, B.A.act c'] B.ph2)
      (ev ![B.actK k b, B.actK k c] h + ev ![B.actK k b, B.actK k c'] h -
        ev ![B.actK k b, B.actK k (c + c')] h) := by
  have p0 : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt k d j i) = 0 := constantCoeff_point
  have c0 : ∀ (i : Fin d), constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) i) = 0 :=
    constantCoeff_addOf (constantCoeff_FK B) (p0 1) (p0 2)
  have h0 : constantCoeff h = 0 := by
    rw [← constantCoeff_ev_eq (cz2 (x := (0 : Pt k 1 d)) (fun _ => by simp) (constantCoeff_point 0)),
      hh.ax0, map_zero]
  have key := isExpOf_ev (cz3 (B.A.const b) (B.A.const c) (B.A.const c')) (by
    rw [map_sub, map_add, constantCoeff_ev_eq (cz2 (p0 0) (p0 1)), constantCoeff_ev_eq (cz2 (p0 0) (p0 2)),
      constantCoeff_ev_eq (cz2 (p0 0) c0), h0]
    simp) hh.ph2
  have e : (fun j i => FB.toK k ((![B.A.act b, B.A.act c, B.A.act c'] : Fin 3 → Pt R 1 d) j i)) =
      ![B.actK k b, B.actK k c, B.actK k c'] := by
    funext j; fin_cases j <;> rfl
  have hb := cz3 (constantCoeff_actK (k := k) B b) (constantCoeff_actK (k := k) B c)
    (constantCoeff_actK (k := k) B c')
  rw [e, ev_minus hb, ev_plus hb, germEv_germEv_two_points (p0 0) (p0 1) hb, germEv_germEv_two_points (p0 0) (p0 2) hb, germEv_germEv_two_points (p0 0) c0 hb,
    ev_addOf _ (p0 1) (p0 2) hb, ev_point_fun hb, ev_point_fun hb, ev_point_fun hb] at key
  rw [actK_add]
  exact key
end GlobalTheory.FrameGeo
