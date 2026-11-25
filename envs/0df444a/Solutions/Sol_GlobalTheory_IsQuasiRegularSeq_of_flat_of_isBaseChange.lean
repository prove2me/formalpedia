-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.of_flat_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:58.044881+00:00
-- url     : https://prove2.me/submissions/bda62d9e-282e-4a43-9ae7-ea4e645e2ae7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_linearEquiv
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_baseChange

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
variable {N : Type*} [AddCommGroup N] [Module R N]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution [Module S N] [IsScalarTower R S N]
    [Module.Flat R S] {g : M →ₗ[R] N} (hg : IsBaseChange S g) {f : ι → R}
    (h : IsQuasiRegularSeq M f) : IsQuasiRegularSeq N fun i => algebraMap R S (f i) :=
  (h.baseChange S).of_linearEquiv hg.equiv
end IsQuasiRegularSeq
end GlobalTheory
