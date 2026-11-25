-- Prove2me | solution 1 for GlobalTheory.ReducedAlg.isReduced_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:02.770489+00:00
-- url     : https://prove2.me/submissions/1ebcdec2-fb85-4b69-83a7-f08a91bc07b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_tensor_of_forall_prime
import Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_field_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.ReducedAlg
namespace GlobalTheory.ReducedAlg
theorem _root_.solution {k : Type*} [Field k] [PerfectField k] (A B : Type*)
    [CommRing A] [Algebra k A] [IsReduced A] [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  refine isReduced_tensor_of_forall_prime A B (fun p _ => ?_)
  have : IsReduced (FractionRing (B ⧸ p) ⊗[k] A) := isReduced_field_tensor (FractionRing (B ⧸ p)) A
  have : IsReduced (A ⊗[k] FractionRing (B ⧸ p)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p)))
      (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p))).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k (B ⧸ p) (FractionRing (B ⧸ p))))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective (B ⧸ p) _))
end GlobalTheory.ReducedAlg
