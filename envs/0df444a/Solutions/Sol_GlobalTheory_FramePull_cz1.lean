-- Prove2me | solution 1 for GlobalTheory.FramePull.cz1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:47.35592+00:00
-- url     : https://prove2.me/submissions/54c8934b-df03-4ba2-bdbf-c76600358790

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond

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
theorem _root_.solution {n : ℕ} {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    ∀ j i, constantCoeff ((![x] : Fin 1 → Pt R n d) j i) = 0 := by
  intro j i; fin_cases j; exact hx i
end GlobalTheory.FramePull
