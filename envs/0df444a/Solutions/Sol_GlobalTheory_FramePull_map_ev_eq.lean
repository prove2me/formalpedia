-- Prove2me | solution 1 for GlobalTheory.FramePull.map_ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:01.083333+00:00
-- url     : https://prove2.me/submissions/f7571918-5bdd-4f10-bce5-6c9d2a340e3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_hasSubst_points

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
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.FramePull
theorem _root_.solution {k : Type} [CommRing k] (φ : R →+* k) {n m : ℕ} {a : Fin m → Pt R n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d) :
    MvPowerSeries.map φ (ev a f) = ev (fun j i => MvPowerSeries.map φ (a j i)) (MvPowerSeries.map φ f) :=
  map_subst (hasSubst_points ha) f
end GlobalTheory.FramePull
