-- Prove2me | solution 1 for GlobalTheory.T.index_formula_norms_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:06.883925+00:00
-- url     : https://prove2.me/submissions/3f53a9bf-e62a-494a-afa1-e1ed6ea5ee86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexFormulaNormsInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexFormulaNormsInvolutionStatement
import Theorems.Thm_GlobalTheory_QNorm_two_mul_index_sqs_mul_relIndex_norm_involution


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by
  first | exact @GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution | exact GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution | (intros; apply GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution <;> assumption)
end _root_.GlobalTheory.T
