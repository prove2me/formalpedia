-- Prove2me | solution 1 for GlobalTheory.Nef.place_aeval_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:40.902169+00:00
-- url     : https://prove2.me/submissions/66ceb0de-4755-457e-91da-bd6642b8104a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOne
import Theorems.Thm_GlobalTheory_Nef_place_aeval_le_one

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
noncomputable section
open GlobalTheory GlobalTheory.Nef
open Polynomial
variable {k L : Type} [Field k] [Field L] [Algebra k L]
namespace GlobalTheory.Nef
theorem _root_.solution (x : L) (u : Place k L) (hx : u.1 x < 1) (q : k[X]) (hq : q.coeff 0 ≠ 0) :
    u.1 (aeval x q) = 1 := by
  have h1 : u.1 (algebraMap k L (q.coeff 0)) = 1 := u.2.2 _ hq
  have h2 : u.1 (x * aeval x q.divX) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hx (place_aeval_le_one x u hx.le _)
  conv_lhs => rw [← X_mul_divX_add q]
  rw [map_add, map_mul, aeval_X, aeval_C, Valuation.map_add_eq_of_lt_right u.1 (by rw [h1]; exact h2), h1]
end GlobalTheory.Nef
