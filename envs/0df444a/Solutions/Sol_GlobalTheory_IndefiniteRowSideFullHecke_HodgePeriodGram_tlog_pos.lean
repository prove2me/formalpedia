-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:11.416847+00:00
-- url     : https://prove2.me/submissions/da37ffb9-59f4-47a2-9ac3-ee65ee60e5d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
open GlobalTheory.HermFrame
variable {n a g : ℕ}
open Matrix Complex Filter Topology
open scoped ComplexOrder
variable {n a g : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
theorem _root_.solution {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog w :=
  div_pos (neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr h0) h1)) (by positivity)
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
end GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
