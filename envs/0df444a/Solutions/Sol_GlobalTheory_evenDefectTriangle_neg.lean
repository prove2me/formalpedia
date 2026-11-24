-- Prove2me | solution 1 for GlobalTheory.evenDefectTriangle_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:13.038889+00:00
-- url     : https://prove2.me/submissions/7ad35453-37a8-4082-a1a1-ae72cf546372

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CubicalFunctionOfHomomorphism
import Theorems.Thm_GlobalTheory_two_mul_evenDefectTriangle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℤ) : evenDefectTriangle (-n) = evenDefectTriangle n + n := by
  have h1 := two_mul_evenDefectTriangle (-n)
  have h2 := two_mul_evenDefectTriangle n
  have : 2 * evenDefectTriangle (-n) = 2 * (evenDefectTriangle n + n) := by
    rw [h1, mul_add, h2]; ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) this
end GlobalTheory
