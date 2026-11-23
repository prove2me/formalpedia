-- Prove2me | solution 1 for GlobalTheory.e8_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:10.003287+00:00
-- url     : https://prove2.me/submissions/6d4a2b7d-2613-4c02-a5ae-7bf7d14273db

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
theorem _root_.solution : E8ᵀ = E8 := CartanMatrix.E₈_transpose
end GlobalTheory
