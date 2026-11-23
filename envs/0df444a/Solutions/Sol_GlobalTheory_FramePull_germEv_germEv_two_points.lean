-- Prove2me | solution 1 for GlobalTheory.FramePull.germEv_germEv_two_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:18.550131+00:00
-- url     : https://prove2.me/submissions/6afd09c6-dfb5-4a1d-b20a-25943920b7b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_ev_comp
import Theorems.Thm_GlobalTheory_FramePull_cz2

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
theorem _root_.solution {n l : ℕ} {x y : Pt R n d} {b : Fin n → Pt R l d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS R 2 d) :
    ev b (ev ![x, y] f) = ev ![fun i => ev b (x i), fun i => ev b (y i)] f := by
  rw [ev_comp (cz2 hx hy) hb]
  congr 1
  funext j; fin_cases j <;> rfl
end GlobalTheory.FramePull
