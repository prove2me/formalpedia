-- Prove2me | solution 1 for GlobalTheory.evenDefectTriangle_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:12.22786+00:00
-- url     : https://prove2.me/submissions/860692a5-9297-4a2c-b05a-7eabebb120ef

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
theorem _root_.solution (a a' b : ℤ) :
    evenDefectTriangle (a + a' + b) + evenDefectTriangle a + evenDefectTriangle a'
      + evenDefectTriangle b
      = evenDefectTriangle (a + a') + evenDefectTriangle (a + b) + evenDefectTriangle (a' + b) := by
  have h1 := two_mul_evenDefectTriangle (a + a' + b)
  have h2 := two_mul_evenDefectTriangle a
  have h3 := two_mul_evenDefectTriangle a'
  have h4 := two_mul_evenDefectTriangle b
  have h5 := two_mul_evenDefectTriangle (a + a')
  have h6 := two_mul_evenDefectTriangle (a + b)
  have h7 := two_mul_evenDefectTriangle (a' + b)
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  linear_combination h1 + h2 + h3 + h4 - h5 - h6 - h7
end GlobalTheory
