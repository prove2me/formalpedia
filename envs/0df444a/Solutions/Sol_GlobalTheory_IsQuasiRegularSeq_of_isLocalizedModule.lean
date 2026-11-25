-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.of_isLocalizedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:38.444333+00:00
-- url     : https://prove2.me/submissions/3b7453a0-4ecd-4f68-a109-7b707ded296a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_flat_of_isBaseChange

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
    (T : Submonoid R) [IsLocalization T S] (g : M →ₗ[R] N) [IsLocalizedModule T g] {f : ι → R}
    (h : IsQuasiRegularSeq M f) : IsQuasiRegularSeq N fun i => algebraMap R S (f i) :=
  have : Module.Flat R S := IsLocalization.flat S T
  h.of_flat_of_isBaseChange S (IsLocalizedModule.isBaseChange T S g)
end IsQuasiRegularSeq
end GlobalTheory
