-- Prove2me | solution 1 for GlobalTheory.FramePull.germ_ev_ev_single_point_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:46.409961+00:00
-- url     : https://prove2.me/submissions/4a635c41-43da-44b9-8c8a-939a5a336a66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_ev_comp
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
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.FramePull
theorem _root_.solution {n l : ℕ} {x : Pt R n d} {b : Fin n → Pt R l d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS R 1 d) :
    ev b (ev ![x] f) = ev ![fun i => ev b (x i)] f := by
  rw [ev_comp (cz1 hx) hb]
  congr 1
  funext j; fin_cases j; rfl
end GlobalTheory.FramePull
