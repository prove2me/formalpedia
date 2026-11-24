-- Prove2me | solution 1 for GlobalTheory.IterGain.nil_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:38.684095+00:00
-- url     : https://prove2.me/submissions/1e1ad49c-68c0-46fd-a2c6-cd00a5f1bc8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.IterGain
namespace GlobalTheory.IterGain
theorem _root_.solution {ι : Type} [DecidableEq ι] (B : Finset ι) (k : ℕ) : [] ∈ words B k := by
  cases k <;> simp [words]
end GlobalTheory.IterGain
