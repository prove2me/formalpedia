-- Prove2me | solution 1 for GlobalTheory.isLocalizedModule_invariantsMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:28.420671+00:00
-- url     : https://prove2.me/submissions/214f366e-92a7-4273-a3ae-fc517534a5dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isBaseChange_invariantsMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']
variable {G : Type*} [Group G]
namespace GlobalTheory
theorem _root_.solution [Finite G] (T : Submonoid R) [IsLocalization T S]
    (ρ : Representation R G M) (ρ' : Representation S G M') (f : M →ₗ[R] M')
    [IsLocalizedModule T f] (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    IsLocalizedModule T (invariantsMap ρ ρ' f hf) :=
  haveI := IsLocalization.flat S T
  (isLocalizedModule_iff_isBaseChange T S _).mpr <| isBaseChange_invariantsMap S ρ ρ' f
    ((isLocalizedModule_iff_isBaseChange T S f).mp ‹_›) hf
end GlobalTheory
