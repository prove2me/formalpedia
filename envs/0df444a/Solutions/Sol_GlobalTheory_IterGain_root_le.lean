-- Prove2me | solution 1 for GlobalTheory.IterGain.root_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:58.81861+00:00
-- url     : https://prove2.me/submissions/c3825c85-8663-458a-adca-c6dcae922eb9

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
theorem _root_.solution {x y : ℝ} {m : ℕ} (hm : m ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ m ≤ y ^ m) :
    x ≤ y := (pow_le_pow_iff_left₀ hx hy hm).1 h
end GlobalTheory.IterGain
