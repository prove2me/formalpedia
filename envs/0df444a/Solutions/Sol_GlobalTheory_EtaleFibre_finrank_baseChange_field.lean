-- Prove2me | solution 1 for GlobalTheory.EtaleFibre.finrank_baseChange_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:41.04012+00:00
-- url     : https://prove2.me/submissions/d62e067e-a762-4783-8a8b-81dfaa597075

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleFibreEmbeddingsCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaleFibre
namespace GlobalTheory.EtaleFibre
theorem _root_.solution (A M L : Type*) [CommRing A] [IsDomain A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Flat A M] [Field L] [Algebra A L] :
    Module.finrank L (L ⊗[A] M) = Module.finrank A M := by
  have h := Module.rankAtStalk_baseChange (R := A) (M := M) (S := L) (⊥ : PrimeSpectrum L)
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq,
    Ideal.finrank_fiber_eq_finrank] at h
  exact h
end GlobalTheory.EtaleFibre
