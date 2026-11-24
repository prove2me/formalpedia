-- Prove2me | solution 1 for GlobalTheory.ValuedPrincipal.val_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:11:43.942003+00:00
-- url     : https://prove2.me/submissions/043d1f5d-082e-4f4b-b556-840584f1fd40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuedPrincipal
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace GlobalTheory.ValuedPrincipal
theorem _root_.solution {t : F} {r : ℚ} (h : v t = (r : WithTop ℚ)) (k : ℕ) :
    v (t ^ k) = (((k : ℚ) * r : ℚ) : WithTop ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, v.map_mul, ih, h, ← WithTop.coe_add]
    congr 1
    push_cast
    ring
end GlobalTheory.ValuedPrincipal
