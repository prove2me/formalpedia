-- Prove2me | solution 1 for GlobalTheory.T.functionFieldPlace_localIndex_scaled_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:09.241291+00:00
-- url     : https://prove2.me/submissions/333214f7-8b9b-40fc-b7f3-12f200acdad8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexScaledUniformiser
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexColengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexScaledUniformiserStatement
import Theorems.Thm_GlobalTheory_Nef_local_index_scaled


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (M : Matrix (Fin n) (Fin n) F) (d : ℕ), M.det ≠ 0 →
    (∀ i j, v.1 (M⁻¹ i j) ≤ WithZero.exp (d : ℤ)) →
    ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = n * d - ord v M.det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (d : ℤ)) → φ p = 0 →
        ∀ i, v.1 (M.mulVec p i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.local_index_scaled | exact GlobalTheory.Nef.local_index_scaled | (intros; apply GlobalTheory.Nef.local_index_scaled <;> assumption)
end _root_.GlobalTheory.T
