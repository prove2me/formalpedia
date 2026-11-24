-- Prove2me | solution 1 for GlobalTheory.localized_saturation_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:07.355525+00:00
-- url     : https://prove2.me/submissions/c68853a9-c24e-421a-bb5a-f2e208be9aa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

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
theorem _root_.solution [IsDomain R] (P : Ideal R) [P.IsPrime] (N : Submodule R M) :
    (saturation N).localized P.primeCompl = saturation (N.localized P.primeCompl) := localized'_saturation (Localization P.primeCompl) P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl M) P.primeCompl_le_nonZeroDivisors N
end GlobalTheory
