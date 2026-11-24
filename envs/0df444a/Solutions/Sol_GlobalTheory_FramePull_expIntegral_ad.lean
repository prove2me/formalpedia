-- Prove2me | solution 1 for GlobalTheory.FramePull.expIntegral_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:11:35.190814+00:00
-- url     : https://prove2.me/submissions/6efc22bd-7b64-4637-bfe2-b964cbb318a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_ev_minus
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_ev_eq
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_point
import Theorems.Thm_GlobalTheory_FramePull_cz2
import Theorems.Thm_GlobalTheory_FramePull_germEv_germEv_two_points
import Theorems.Thm_GlobalTheory_FramePull_ev_point_fun
import Theorems.Thm_GlobalTheory_FramePull_ev_comp1
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_comp1
import Theorems.Thm_GlobalTheory_FramePull_expIntegral_ev
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_actK
import Theorems.Thm_GlobalTheory_FramePull_actK_mul

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
theorem _root_.solution (hh : B.IsCanonGauge k h) (a b c : O) :
    ExpIntegral R (ev ![B.actK k (a * b), B.actK k c] h - ev ![B.actK k b, B.actK k (star a * c)] h) := by
  have p0 : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt k d j i) = 0 := constantCoeff_point
  have c0 : ∀ (e : O) (j : Fin 2) (i : Fin d), constantCoeff (comp1 (B.actK k e) (pt k d j) i) = 0 :=
    fun e j => constantCoeff_comp1 (constantCoeff_actK B e) (p0 j)
  have w1 : constantCoeff (B.ad a) = 1 := by
    rw [← constantCoeff_ev_eq (cz2 (x := (0 : Pt R 1 d)) (fun _ => by simp) (constantCoeff_point 0)),
      B.adjoint_zero_fst, map_one]
  have key := expIntegral_ev (cz2 (B.A.const b) (B.A.const c)) w1 (by
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
end GlobalTheory.FramePull
