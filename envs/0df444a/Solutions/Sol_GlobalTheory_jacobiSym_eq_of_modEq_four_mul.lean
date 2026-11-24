-- Prove2me | solution 1 for GlobalTheory.jacobiSym_eq_of_modEq_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:23.454557+00:00
-- url     : https://prove2.me/submissions/18115e87-8afc-49bc-a19f-874867eccc8c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JacobiSymEqOfModEqFourMul

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
theorem _root_.solution (a q q' : ℕ) (hq : Odd q) (hq' : Odd q')
    (h : q ≡ q' [MOD 4 * a]) : jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) q' := by
  rw [jacobiSym.mod_right' a hq, jacobiSym.mod_right' a hq']
  unfold Nat.ModEq at h
  rw [h]
end GlobalTheory
