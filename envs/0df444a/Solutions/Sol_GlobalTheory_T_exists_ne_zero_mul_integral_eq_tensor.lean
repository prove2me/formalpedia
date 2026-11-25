-- Prove2me | solution 1 for GlobalTheory.T.exists_ne_zero_mul_integral_eq_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:42:19.759517+00:00
-- url     : https://prove2.me/submissions/d30f562d-76f6-45e0-be63-2f077091c8a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegralStatement
import Theorems.Thm_GlobalTheory_DiscConductor_discr_mul_mem_of_isIntegral


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
theorem _root_.solution : ∀ (T U C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T] [CommRing U] [IsDomain U] [IsIntegrallyClosed U] [Algebra T U] [Module.Flat T U] [CommRing C] [IsDomain C] [Algebra T C] [Module.Finite T C], Function.Injective (algebraMap T U) → Function.Injective (algebraMap T C) → ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c → ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s = algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  first | exact @GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral | exact GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral | (intros; apply GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral <;> assumption)
end _root_.GlobalTheory.T
