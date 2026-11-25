-- Prove2me | solution 1 for GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:56.566037+00:00
-- url     : https://prove2.me/submissions/eb9d6628-df48-46ba-bbd0-2009376f5b83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexNormMulRelIndexSqsKerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulIndexSqsInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexFormulaNormsInvolution
import Theorems.Thm_GlobalTheory_T_two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker
import Theorems.Thm_P2M_GlobalTheory_T_relIndex_norm_mul_relIndex_sqs_ker__85d8b10d9937


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
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by
  intro A _ σ ε h1 h2 h3 h4 h5 h6
  have hn := GlobalTheory.T.relIndex_norm_mul_relIndex_sqs_ker' A σ h1 h2
  have hs := GlobalTheory.T.two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker A σ ε h1 h2 h3 h4 h5 h6
  rw [hs, sq, mul_assoc, mul_comm ((sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker), hn]
end GlobalTheory.QNorm
