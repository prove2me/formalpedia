-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosedIn_of_injective_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:35.917022+00:00
-- url     : https://prove2.me/submissions/615764c8-d107-4b71-bf20-3f634c23aeaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R R' K : Type*) [CommRing R] [CommRing R']
    [CommRing K] [Algebra R R'] [Algebra R K] [Algebra R' K] [IsScalarTower R R' K]
    [IsFractionRing R K] [IsIntegrallyClosed R] (hK : Function.Injective (algebraMap R' K)) :
    IsIntegrallyClosedIn R R' := by
  have hKR : IsIntegrallyClosedIn R K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp ‹_›
  exact (IsScalarTower.toAlgHom R R' K).isIntegrallyClosedIn hK hKR
end GlobalTheory
