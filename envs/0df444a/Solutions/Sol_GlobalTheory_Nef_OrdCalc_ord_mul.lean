-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.ord_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:13:38.900004+00:00
-- url     : https://prove2.me/submissions/cf68a200-89fc-4f46-b4f8-737ebc84cc35

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
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (vne v hx) (vne v hy)]; ring
end GlobalTheory.Nef.OrdCalc
