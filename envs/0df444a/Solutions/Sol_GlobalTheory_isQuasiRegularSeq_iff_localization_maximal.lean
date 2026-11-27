-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_iff_localization_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:56.643503+00:00
-- url     : https://prove2.me/submissions/b018b852-9f12-49a2-87c5-886a0d3467cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_algebraMap_iff
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule_maximal

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
theorem _root_.solution (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ (P : Ideal R) [P.IsMaximal], Ideal.span (Set.range f) ≤ P →
      IsQuasiRegularSeq (LocalizedModule P.primeCompl M)
        fun i => algebraMap R (Localization.AtPrime P) (f i) :=
  ⟨fun h P _ _ => h.of_isLocalizedModule _ P.primeCompl (LocalizedModule.mkLinearMap _ M),
    fun h => .of_isLocalizedModule_maximal (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      fun P _ hP => (isQuasiRegularSeq_algebraMap_iff _ f).mp (h P hP)⟩
end GlobalTheory
