-- Prove2me | solution 1 for GlobalTheory.FramePull.expIntegral_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:48.729674+00:00
-- url     : https://prove2.me/submissions/13c465c5-9b3c-4eb2-95b2-3dcc96c97078

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_ev_eq
import Theorems.Thm_GlobalTheory_FramePull_map_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp


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
variable (R : Type) [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {R}
namespace GlobalTheory.FramePull
theorem _root_.solution {m : ℕ} {a : Fin m → Pt R 1 d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    {w : PS R m d} (w1 : constantCoeff w = 1) {f : PS k m d} (f0 : constantCoeff f = 0)
    (hw : FB.toK k w = FB.expS k f) :
    ExpIntegral R (ev (fun j i => FB.toK k (a j i)) f) := by
  have ha' : ∀ j i, constantCoeff (FB.toK k (a j i)) = 0 := fun j i => by simp [FB.toK, ha]
  refine ⟨by rw [constantCoeff_ev_eq ha', f0], ev a w, by rw [constantCoeff_ev_eq ha, w1], ?_⟩
  have e1 : FB.toK k (ev a w) = ev (fun j i => FB.toK k (a j i)) (FB.toK k w) := map_ev_eq _ ha w
  rw [e1, hw]
  unfold ev FB.expS
  exact WickVanishing.subst_exp (fun p : Fin m × Fin d => FB.toK k (a p.1 p.2)) (fun p => ha' p.1 p.2) f0
end GlobalTheory.FramePull
