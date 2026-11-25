-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.formalSeriesValueAtThreePoints_genericPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:48:13.158202+00:00
-- url     : https://prove2.me/submissions/4d27ff78-76f1-4f85-8d0a-a891f2e88a62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_sb_gen

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
theorem _root_.solution (f : PS k 3 d) : E3 f (gen 0) (gen 1) (gen 2) = f := by
  show sb ![gen 0, gen 1, gen 2] f = f
  have h : (![gen 0, gen 1, gen 2] : Fin 3 → Q k d 3) = gen := by
    funext j
    fin_cases j <;> rfl
  rw [h, sb_gen]
end GlobalTheory.FrameBiextId
