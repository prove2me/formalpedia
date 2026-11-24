-- Prove2me | solution 1 for GlobalTheory.isDedekindDomain_integralClosure_of_dimensionLEOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:37.689907+00:00
-- url     : https://prove2.me/submissions/d5058c2f-b138-47e2-895b-697ac57f5e6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_krullAkizuki

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
  (K : Type*) {L : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
include K
namespace GlobalTheory
theorem _root_.solution :
    IsDedekindDomain (integralClosure A L) := by
  obtain ⟨h1, h2⟩ := krullAkizuki K (integralClosure A L)
  have h3 : IsIntegrallyClosed (integralClosure A L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  have h4 : IsDedekindRing (integralClosure A L) := { }
  exact { }
end GlobalTheory
