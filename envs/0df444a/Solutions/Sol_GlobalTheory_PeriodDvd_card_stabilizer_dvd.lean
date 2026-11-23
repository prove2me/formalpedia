-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.card_stabilizer_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:02.556687+00:00
-- url     : https://prove2.me/submissions/92945d3c-c28a-4eb4-8f93-8b30ee5f3585

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] (I : Finset (ZMod d)) :
    Nat.card (AddAction.stabilizer (ZMod d) I) ∣ d := by
  have := AddSubgroup.card_addSubgroup_dvd_card (AddAction.stabilizer (ZMod d) I)
  rwa [Nat.card_zmod] at this
end GlobalTheory.PeriodDvd
