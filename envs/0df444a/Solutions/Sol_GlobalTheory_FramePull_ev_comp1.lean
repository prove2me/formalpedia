-- Prove2me | solution 1 for GlobalTheory.FramePull.ev_comp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:49:44.422862+00:00
-- url     : https://prove2.me/submissions/cc481991-c430-4709-9d48-4c432182725d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_germ_ev_ev_single_point_comp

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
theorem _root_.solution {n l : ℕ} (φ : Pt R 1 d) {x : Pt R n d} {b : Fin n → Pt R l d}
    (hx : ∀ i, constantCoeff (x i) = 0) (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (comp1 φ x i)) = comp1 φ (fun i => ev b (x i)) :=
  funext fun i => germ_ev_ev_single_point_comp hx hb (φ i)
end GlobalTheory.FramePull
