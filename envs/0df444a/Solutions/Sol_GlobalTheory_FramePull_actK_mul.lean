-- Prove2me | solution 1 for GlobalTheory.FramePull.actK_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:19.25887+00:00
-- url     : https://prove2.me/submissions/37568d98-282e-49e7-896d-d1cf542984bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_map_ev_eq
import Theorems.Thm_GlobalTheory_FramePull_cz1

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
omit [Algebra ℚ k]
namespace GlobalTheory.FramePull
theorem _root_.solution (a b : O) : B.actK k (a * b) = comp1 (B.actK k a) (B.actK k b) := by
  funext i
  simp only [FB.actK, B.A.mul_act, comp1]
  rw [map_ev_eq _ (cz1 (B.A.const b))]
  congr 1
  funext j; fin_cases j; rfl
end GlobalTheory.FramePull
