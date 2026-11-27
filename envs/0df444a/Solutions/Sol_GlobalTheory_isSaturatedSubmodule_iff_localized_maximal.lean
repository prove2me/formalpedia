-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_iff_localized_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:31.559633+00:00
-- url     : https://prove2.me/submissions/9b7ba5b1-82d0-43b3-9ad0-dbf9b3bbbf11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_localized_saturation_atPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R) [IsLocalization p S]
  {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
  (f : M →ₗ[R] Mp) [IsLocalizedModule p f]
namespace GlobalTheory
theorem _root_.solution [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔
      ∀ (P : Ideal R) [P.IsMaximal], IsSaturatedSubmodule (N.localized P.primeCompl) := by
  constructor
  · intro h P _
    exact h.localized' (Localization P.primeCompl) P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl M) P.primeCompl_le_nonZeroDivisors
  · intro h
    rw [isSaturatedSubmodule_iff_le]
    refine Submodule.le_of_localization_maximal (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M) fun P _ => ?_
    exact (congrArg (Submodule.restrictScalars R)
      ((localized_saturation_atPrime P N).trans (h P).saturation_eq)).le
end GlobalTheory
