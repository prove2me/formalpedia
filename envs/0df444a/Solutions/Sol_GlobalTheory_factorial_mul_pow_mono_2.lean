-- Prove2me | solution 2 for GlobalTheory.factorial_mul_pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:36.611627+00:00
-- url     : https://prove2.me/submissions/cdb1dcfc-b62e-4305-944b-8fe0ff6401af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {p N : ℕ} (hp : p ≤ N) {r : ℝ} (hr : 1 ≤ r) :
    ((p + 1)! : ℝ) * r ^ (2 * p + 1) ≤ (N + 1)! * r ^ (2 * N + 1) := by
  gcongr
end GlobalTheory
