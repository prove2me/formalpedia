-- Prove2me | solution 1 for GlobalTheory.T.exists_injective_tensor_into_tensor_fractionFields
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:06.741031+00:00
-- url     : https://prove2.me/submissions/a7c610f8-2925-4e73-a9dc-14bde222ffdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatTensorEmbedsTensorFractionFields
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatTensorEmbedsTensorFractionFieldsStatement
import Theorems.Thm_GlobalTheory_flat_tensor_embeds_tensor_fractionFields


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
theorem _root_.solution : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U], ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧ ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by
  first | exact @GlobalTheory.flat_tensor_embeds_tensor_fractionFields | exact GlobalTheory.flat_tensor_embeds_tensor_fractionFields | (intros; apply GlobalTheory.flat_tensor_embeds_tensor_fractionFields <;> assumption)
end _root_.GlobalTheory.T
