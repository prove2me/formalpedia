-- Prove2me | solution 1 for GlobalTheory.ReducedAlg.isReduced_field_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:35.220537+00:00
-- url     : https://prove2.me/submissions/4e77f7ba-aa07-45b0-9e05-d4d1a88aec45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_tensor_of_forall_prime
import Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_field_tensor_domain

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
theorem _root_.solution {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (K ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).2 hB⟩
  refine isReduced_tensor_of_forall_prime K B (fun p _ => ?_)
  have : Algebra.FiniteType k (B ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p)
      (Ideal.Quotient.mkₐ_surjective k p)
  exact isReduced_field_tensor_domain K (B ⧸ p)
end GlobalTheory.ReducedAlg
