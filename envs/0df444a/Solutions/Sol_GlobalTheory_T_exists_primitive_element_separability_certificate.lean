-- Prove2me | solution 1 for GlobalTheory.T.exists_primitive_element_separability_certificate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:11:01.720861+00:00
-- url     : https://prove2.me/submissions/bddb534a-30af-4ad6-9c84-34c00f13ddc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificate
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificateStatement
import Theorems.Thm_GlobalTheory_SepPoint_exists_primitive_sep_certificate


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
theorem _root_.solution : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F), IsTranscendenceBasis k ((↑) : s → F) → Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F → ∀ T : Finset F, ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧ ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧ ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)), U * minpoly (Algebra.adjoin k (s : Set F)) θ + V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) = Polynomial.C H ∧ ∀ x ∈ T, (H : F) * x ∈ Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
  first | exact @GlobalTheory.SepPoint.exists_primitive_sep_certificate | exact GlobalTheory.SepPoint.exists_primitive_sep_certificate | (intros; apply GlobalTheory.SepPoint.exists_primitive_sep_certificate <;> assumption)
end _root_.GlobalTheory.T
