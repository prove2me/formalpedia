-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:13:36.687677+00:00
-- url     : https://prove2.me/submissions/8812f555-efb5-47a3-b61c-89003571cec3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_vne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.OrdCalc
theorem _root_.solution (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) one_ne_zero, WithZero.log_one, neg_nonneg]
end GlobalTheory.Nef.OrdCalc
