-- Prove2me | solution 1 for GlobalTheory.finite_of_isIntegralClosure_dedekind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:13.545513+00:00
-- url     : https://prove2.me/submissions/9cc1c60e-9ffc-4a89-a397-0db98decc61e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable (o R : Type*) [CommRing o] [IsDedekindDomain o] [CommRing R] [Algebra o R]
  [Algebra.FiniteType o R]
namespace GlobalTheory
theorem _root_.solution [CharZero o] [IsDomain R] [FaithfulSMul o R]
    (K L C : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L] [CommRing C] [Algebra R C]
    [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L] : Module.Finite R C :=
  haveI := finite_integralClosure_dedekind o R K L
  .equiv (IsIntegralClosure.equiv R (integralClosure R L) L C).toLinearEquiv
end GlobalTheory
