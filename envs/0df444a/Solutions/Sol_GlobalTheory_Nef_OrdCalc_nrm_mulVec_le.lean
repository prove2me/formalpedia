-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.nrm_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:56.787531+00:00
-- url     : https://prove2.me/submissions/64de8023-2010-404e-b3a8-eceabff2c25d

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
theorem _root_.solution (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : nrm v (u.mulVec x) ≤ nrm v x := by
  unfold nrm
  apply Finset.sup_le; intro i _
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (u i j) * v.1 (x j) ≤ 1 * Finset.univ.sup (fun i => v.1 (x i)) :=
        mul_le_mul' (hu i j) (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j))
  _ = _ := one_mul _
end GlobalTheory.Nef.OrdCalc
