-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:37.276788+00:00
-- url     : https://prove2.me/submissions/afba455f-8c4f-4f06-8ffb-ab8b3ad8c99a

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
theorem _root_.solution (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) (vne v hy), neg_le_neg_iff]
end GlobalTheory.Nef.OrdCalc
