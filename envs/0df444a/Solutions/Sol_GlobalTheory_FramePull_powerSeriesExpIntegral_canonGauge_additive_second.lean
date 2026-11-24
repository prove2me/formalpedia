-- Prove2me | solution 1 for GlobalTheory.FramePull.powerSeriesExpIntegral_canonGauge_additive_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:40.151027+00:00
-- url     : https://prove2.me/submissions/0e17761d-de3e-4b12-90ff-fe05a24143f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_ev_plus
import Theorems.Thm_GlobalTheory_FramePull_ev_minus
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_ev_eq
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_point
import Theorems.Thm_GlobalTheory_FramePull_cz2
import Theorems.Thm_GlobalTheory_FramePull_cz3
import Theorems.Thm_GlobalTheory_FramePull_germEv_germEv_two_points
import Theorems.Thm_GlobalTheory_FramePull_ev_point_fun
import Theorems.Thm_GlobalTheory_FramePull_ev_addOf
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_addOf
import Theorems.Thm_GlobalTheory_FramePull_expIntegral_ev
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_actK
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_FK
import Theorems.Thm_GlobalTheory_FramePull_actK_add

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
open GlobalTheory GlobalTheory.FramePull
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O)
variable {B} {h : PS k 2 d}
namespace GlobalTheory.FramePull
theorem _root_.solution (hh : B.IsCanonGauge k h) (b c c' : O) :
    ExpIntegral R (ev ![B.actK k b, B.actK k c] h + ev ![B.actK k b, B.actK k c'] h -
      ev ![B.actK k b, B.actK k (c + c')] h) := by
  have p0 : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt k d j i) = 0 := constantCoeff_point
  have c0 : ∀ (i : Fin d), constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) i) = 0 :=
    constantCoeff_addOf (constantCoeff_FK B) (p0 1) (p0 2)
  have h0 : constantCoeff h = 0 := by
    rw [← constantCoeff_ev_eq (cz2 (x := (0 : Pt k 1 d)) (fun _ => by simp) (constantCoeff_point 0)),
      hh.ax0, map_zero]
  have w1 : constantCoeff B.ph2 = 1 := by
    rw [← constantCoeff_ev_eq (cz3 (x := (0 : Pt R 2 d)) (fun _ => by simp) (constantCoeff_point 0)
      (constantCoeff_point 1)), B.cocycleRight_zero_fst, map_one]
  have key := expIntegral_ev (cz3 (B.A.const b) (B.A.const c) (B.A.const c')) w1 (by
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
end GlobalTheory.FramePull
