-- Prove2me | solution 1 for GlobalTheory.T.laurent_finite_of_triangular_signed_indicators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:58.947689+00:00
-- url     : https://prove2.me/submissions/e4db9633-34dd-4673-b412-a3d9b155f44a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicatorsStatement
import Theorems.Thm_GlobalTheory_LaurentFinite_finite_of_triangular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ))), (∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧ ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) → Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  first | exact @GlobalTheory.LaurentFinite.finite_of_triangular | exact GlobalTheory.LaurentFinite.finite_of_triangular | (intros; apply GlobalTheory.LaurentFinite.finite_of_triangular <;> assumption)
end _root_.GlobalTheory.T
