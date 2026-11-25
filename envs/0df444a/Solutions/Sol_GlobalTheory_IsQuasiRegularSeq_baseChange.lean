-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:43.255724+00:00
-- url     : https://prove2.me/submissions/4b9595ff-46f6-4a82-a086-d072f891e177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_algebraMap_iff
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_tensor

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
namespace IsQuasiRegularSeq
theorem _root_.solution [Module.Flat R S] {f : ι → R} (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (S ⊗[R] M) fun i => algebraMap R S (f i) :=
  (isQuasiRegularSeq_algebraMap_iff S f).mpr (h.tensor S)
end IsQuasiRegularSeq
end GlobalTheory
