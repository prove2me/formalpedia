-- Prove2me | solution 1 for GlobalTheory.T.tensor_residue_unramified_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:24.304906+00:00
-- url     : https://prove2.me/submissions/1a1b0212-7d1b-450c-8ca5-97238cdff5e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorResidueUnramifiedFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorResidueUnramifiedFiniteStatement
import Theorems.Thm_GlobalTheory_tensor_quot_maximalIdeal_finite_formallyUnramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B] [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite → ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified → Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧ Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by
  first | exact @GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified | exact GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified | (intros; apply GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified <;> assumption)
end _root_.GlobalTheory.T
