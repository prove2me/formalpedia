-- Prove2me | solution 1 for GlobalTheory.upperFactor_isUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:21.617065+00:00
-- url     : https://prove2.me/submissions/0e007e10-86fa-490c-a6b8-b42bda1ffa3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
import Theorems.Thm_GlobalTheory_transvection_isUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory
theorem _root_.solution {i j : Fin m} (hji : j < i) (x : k) :
    (upperFactor i j x).BlockTriangular id :=
  (blockTriangular_diagonal _).mul (transvection_isUpper hji x)
end GlobalTheory
