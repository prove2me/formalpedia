-- Prove2me | solution 1 for GlobalTheory.FramePull.ev_addOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:48.873934+00:00
-- url     : https://prove2.me/submissions/e068876e-a8e0-479b-9510-834389b62633

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_germEv_germEv_two_points

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
theorem _root_.solution {n l : ℕ} (F : Fin d → PS R 2 d) {x y : Pt R n d} {b : Fin n → Pt R l d}
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (addOf F x y i)) = addOf F (fun i => ev b (x i)) (fun i => ev b (y i)) :=
  funext fun i => germEv_germEv_two_points hx hy hb (F i)
end GlobalTheory.FramePull
