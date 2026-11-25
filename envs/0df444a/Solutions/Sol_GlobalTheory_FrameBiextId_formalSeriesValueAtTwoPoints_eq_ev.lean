-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.formalSeriesValueAtTwoPoints_eq_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:48:16.19367+00:00
-- url     : https://prove2.me/submissions/f3584df5-e9d0-4afc-b48f-e4f166701f58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace GlobalTheory.FrameBiextId
theorem _root_.solution (f : PS k 2 d) (u v : Q k d n) : E2 f u v = ev ![u.1, v.1] f := by
  show sb ![u, v] f = _
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl
end GlobalTheory.FrameBiextId
