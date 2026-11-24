-- Prove2me | solution 1 for GlobalTheory.E8roots_transpose_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:10.006489+00:00
-- url     : https://prove2.me/submissions/bdea2ad3-78d2-4be0-aa34-0dd52f88f36e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : E8rootsᵀ * E8roots = (4 : ℤ) • E8 := by decide
end GlobalTheory
