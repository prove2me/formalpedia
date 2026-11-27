-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_baseChange_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:51.475864+00:00
-- url     : https://prove2.me/submissions/dd3b09f6-71b4-44e0-8bb7-f6074489b19a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_algebraMap_iff
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_tensor_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
namespace GlobalTheory
theorem _root_.solution [Module.FaithfullyFlat R S] (f : ι → R) :
    (IsQuasiRegularSeq (S ⊗[R] M) fun i => algebraMap R S (f i)) ↔ IsQuasiRegularSeq M f :=
  (isQuasiRegularSeq_algebraMap_iff S f).trans (isQuasiRegularSeq_tensor_iff f S)
end GlobalTheory
