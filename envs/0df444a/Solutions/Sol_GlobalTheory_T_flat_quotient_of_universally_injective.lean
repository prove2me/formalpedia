-- Prove2me | solution 1 for GlobalTheory.T.flat_quotient_of_universally_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:44.935801+00:00
-- url     : https://prove2.me/submissions/308b54a9-3127-41f6-9c60-8e536c038282

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjective
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjectiveStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlatCoker_flat_quotient_range_of_lTensor_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [Module.Flat R B] (f : A →ₗ[R] B), (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) → Module.Flat R (B ⧸ LinearMap.range f) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | exact GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective <;> assumption)
end _root_.GlobalTheory.T
