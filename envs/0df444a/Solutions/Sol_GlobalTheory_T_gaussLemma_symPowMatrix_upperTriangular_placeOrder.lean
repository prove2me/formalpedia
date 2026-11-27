-- Prove2me | solution 1 for GlobalTheory.T.gaussLemma_symPowMatrix_upperTriangular_placeOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:00.706339+00:00
-- url     : https://prove2.me/submissions/cbd32c35-1a0f-4ea3-9f98-9af349d93694

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussLemmaSymPowMatrixUpperTriangularPlaceOrder
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement
import Theorems.Thm_GlobalTheory_Nef_ordVec_symMat_mulVec_triangular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (P : Place k E) (m : ℕ) (A : Matrix (Fin 2) (Fin 2) E), A 1 0 = 0 → A.det ≠ 0 → ∀ (q : Fin (m + 1) → E) (c : E) (s t : Fin m → E), c ≠ 0 → (∀ j, ![s j, t j] ≠ 0) → ∑ i : Fin (m + 1), C (q i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i) = C c * ∏ j, (C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X)) → ordVec P ((symMat m A).mulVec q) = ord P c + ∑ j, ordVec P (A.mulVec ![s j, t j]) := by
  first | exact @GlobalTheory.Nef.ordVec_symMat_mulVec_triangular | exact GlobalTheory.Nef.ordVec_symMat_mulVec_triangular | (intros; apply GlobalTheory.Nef.ordVec_symMat_mulVec_triangular <;> assumption)
end _root_.GlobalTheory.T
