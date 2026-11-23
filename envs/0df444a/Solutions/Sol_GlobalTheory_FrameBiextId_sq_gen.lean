-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.sq_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:38.046881+00:00
-- url     : https://prove2.me/submissions/953bb58a-db11-4634-8504-14c3b8dd272a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
import Theorems.Thm_GlobalTheory_FormalLog_ev_X


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
theorem _root_.solution (b : Fin n → Q k d l) (j : Fin n) : sq b (gen j) = b j := by
  apply Subtype.ext
  funext i
  show sb b (X (j, i)) = (b j).1 i
  rw [sb_apply]
  exact ev_X (czQ b) j i
end GlobalTheory.FrameBiextId
