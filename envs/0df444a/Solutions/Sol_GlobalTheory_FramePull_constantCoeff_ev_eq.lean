-- Prove2me | solution 1 for GlobalTheory.FramePull.constantCoeff_ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:18.326109+00:00
-- url     : https://prove2.me/submissions/f98601f3-beb2-4de7-901e-2947459737ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_hasSubst_points
import Theorems.Thm_GlobalTheory_FramePull_ev_plus

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
theorem _root_.solution {n m : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by
  have e : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  have h0 : constantCoeff (ev a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_points ha) (fun p => ha p.1 p.2) (by simp)
  conv_lhs => rw [e, ev_plus ha, map_add, h0]
  simp [ev]
end GlobalTheory.FramePull
