-- Prove2me | solution 1 for GlobalTheory.conjIdem_sigR_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:08.926988+00:00
-- url     : https://prove2.me/submissions/e36c3b09-1cef-48ca-89b4-5fe82c754861

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPrimeInvolutionOfRingInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CmConjugationOnPrimesProperties
import Theorems.Thm_GlobalTheory_conjIdem_sigR_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [conjIdem_sigR_tmul, conjIdem_sigR_tmul, h]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
end GlobalTheory
