-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:56.36246+00:00
-- url     : https://prove2.me/submissions/68a4f368-922f-44e7-afed-e2d3f0a159ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_algebraMap_iff
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_flat_module

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
theorem _root_.solution [Module.Flat R S] {f : ι → R} (h : IsQuasiRegularSeq R f) :
    IsQuasiRegularSeq S fun i => algebraMap R S (f i) :=
  (isQuasiRegularSeq_algebraMap_iff S f).mpr (h.of_flat_module S)
end IsQuasiRegularSeq
end GlobalTheory
