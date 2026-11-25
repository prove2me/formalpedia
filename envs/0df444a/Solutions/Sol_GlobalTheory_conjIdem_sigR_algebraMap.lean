-- Prove2me | solution 1 for GlobalTheory.conjIdem_sigR_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:01.103943+00:00
-- url     : https://prove2.me/submissions/486dfceb-ba39-4a39-89a9-bc160b1a1ef2

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
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  show sigR R σ (a ⊗ₜ[F] 1) = a ⊗ₜ[F] 1
  rw [conjIdem_sigR_tmul, map_one]
end GlobalTheory
