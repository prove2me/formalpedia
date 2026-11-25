-- Prove2me | solution 1 for GlobalTheory.T.exists_isotropic_graph_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:01.437806+00:00
-- url     : https://prove2.me/submissions/4b527681-00be-424f-b143-113db126c031

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphDetLowerRowNeZeroField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement
import Theorems.Thm_GlobalTheory_exists_isotropic_graph_det_lowerRow_ne_zero_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧ (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  first | exact @GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | exact GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | (intros; apply GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field <;> assumption)
end _root_.GlobalTheory.T
