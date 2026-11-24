-- Prove2me | solution 1 for GlobalTheory.T.frobeniusSubalgebra_counital_comul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:35.498497+00:00
-- url     : https://prove2.me/submissions/f4437a8c-a7c0-4a43-8196-df9bb161184f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSubalgebraCounitalComul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSubalgebraCounitalComulStatement
import Theorems.Thm_GlobalTheory_frobSubalgebra_counit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by
  first | exact @GlobalTheory.frobSubalgebra_counit | exact GlobalTheory.frobSubalgebra_counit | (intros; apply GlobalTheory.frobSubalgebra_counit <;> assumption)
end _root_.GlobalTheory.T
