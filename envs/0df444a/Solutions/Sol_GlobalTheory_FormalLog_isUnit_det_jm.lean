-- Prove2me | solution 1 for GlobalTheory.FormalLog.isUnit_det_jm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:44.547207+00:00
-- url     : https://prove2.me/submissions/25d7d082-6077-400f-820a-784d11cf8e7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_jm_map_cc

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution : IsUnit (JM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, jm_map_cc,
    Matrix.det_one]
  exact isUnit_one
end GlobalTheory.FormalLog
