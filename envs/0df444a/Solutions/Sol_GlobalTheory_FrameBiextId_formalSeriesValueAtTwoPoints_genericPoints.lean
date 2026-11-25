-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.formalSeriesValueAtTwoPoints_genericPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:46:24.49275+00:00
-- url     : https://prove2.me/submissions/5906fc61-4ee5-4001-99d8-43ca12181ce3

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
theorem _root_.solution (f : PS k 2 d) : E2 f (gen 0) (gen 1) = f := by
  show sb ![gen 0, gen 1] f = f
  have h : (![gen 0, gen 1] : Fin 2 → Q k d 2) = gen := by
    funext j
    fin_cases j <;> rfl
  rw [h, sb_gen]
end GlobalTheory.FrameBiextId
