-- Prove2me | solution 1 for GlobalTheory.isFinite_fromNormalization_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:20.953729+00:00
-- url     : https://prove2.me/submissions/44cf1b12-27b9-4110-8f95-ac8c8b95bdc8

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {X Y : Scheme.{u}} {o : CommRingCat.{u}} [IsDedekindDomain o]
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o) [LocallyOfFiniteType g]
include g
namespace GlobalTheory
theorem _root_.solution [IsReduced X] [LocallyOfFiniteType f]
    (hchar : ∀ x ∈ genericPoints X, CharZero (X.residueField x)) :
    IsFinite f.fromNormalization :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ g)
  isFinite_fromNormalization_of_genericPoints f g hchar fun x _ =>
    (LocallyOfFiniteType.stalkMap f x).residueFieldMap
end GlobalTheory
