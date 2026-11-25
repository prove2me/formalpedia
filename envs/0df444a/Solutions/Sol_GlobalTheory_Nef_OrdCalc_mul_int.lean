-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:03:00.570005+00:00
-- url     : https://prove2.me/submissions/30b03740-7083-449a-bb88-0fe9ea8a8d89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.OrdCalc
theorem _root_.solution (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hu' : ∀ i j, v.1 (u' i j) ≤ 1) : ∀ i j, v.1 ((u * u') i j) ≤ 1 := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [map_mul]
  calc v.1 (u i l) * v.1 (u' l j) ≤ 1 * 1 := mul_le_mul' (hu i l) (hu' l j)
  _ = 1 := one_mul _
end GlobalTheory.Nef.OrdCalc
