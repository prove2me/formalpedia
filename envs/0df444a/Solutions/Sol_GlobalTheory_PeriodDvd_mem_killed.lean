-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.mem_killed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:17.762805+00:00
-- url     : https://prove2.me/submissions/7f9f5aa5-4633-4c0e-a667-92e9bc9a2a0b

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
theorem _root_.solution {d : ℕ} [NeZero d] {s : ℕ} {x : ZMod d} : x ∈ killed d s ↔ s • x = 0 := by
  simp [killed]
end GlobalTheory.PeriodDvd
