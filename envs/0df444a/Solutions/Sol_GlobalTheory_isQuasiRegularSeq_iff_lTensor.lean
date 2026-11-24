-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_iff_lTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:22.352799+00:00
-- url     : https://prove2.me/submissions/f949f95e-42f0-4505-ab82-55cf0aa1f02f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_monoToPowGr_injective_iff_lTensor

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
namespace GlobalTheory
theorem _root_.solution (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ a, Function.Injective ((monoToQuotPow f a).lTensor M) :=
  (isQuasiRegularSeq_iff_injective f).trans <| forall_congr' fun a =>
    monoToPowGr_injective_iff_lTensor f a
end GlobalTheory
