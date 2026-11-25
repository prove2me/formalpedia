-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:25.439816+00:00
-- url     : https://prove2.me/submissions/4d763b91-3cef-4329-a319-36db2e6bbed6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule

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
theorem _root_.solution (T : Submonoid R) [IsLocalization T S] {f : ι → R}
    (h : IsQuasiRegularSeq R f) : IsQuasiRegularSeq S fun i => algebraMap R S (f i) :=
  h.of_isLocalizedModule S T (Algebra.linearMap R S)
end IsQuasiRegularSeq
end GlobalTheory
