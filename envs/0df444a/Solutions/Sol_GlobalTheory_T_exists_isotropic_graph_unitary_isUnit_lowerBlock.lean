-- Prove2me | solution 1 for GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:41.307967+00:00
-- url     : https://prove2.me/submissions/5d2742ab-2677-45a1-aa32-78467f05d54a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphUnitaryIsUnitLowerBlock
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphUnitaryIsUnitLowerBlockStatement
import Theorems.Thm_GlobalTheory_exists_isotropic_graph_isUnit_lowerRow


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
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  first | exact @GlobalTheory.exists_isotropic_graph_isUnit_lowerRow | exact GlobalTheory.exists_isotropic_graph_isUnit_lowerRow | (intros; apply GlobalTheory.exists_isotropic_graph_isUnit_lowerRow <;> assumption)
end _root_.GlobalTheory.T
