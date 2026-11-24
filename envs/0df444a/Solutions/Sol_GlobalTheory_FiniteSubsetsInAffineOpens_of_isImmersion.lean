-- Prove2me | solution 1 for GlobalTheory.FiniteSubsetsInAffineOpens.of_isImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:05:58.043874+00:00
-- url     : https://prove2.me/submissions/ca3cfb27-c2ed-4aae-bb42-068d1d93f3b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_FiniteSubsetsInAffineOpens_of_isAffineHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {X Y : Scheme.{u}}
open GlobalTheory.FiniteSubsetsInAffineOpens
namespace GlobalTheory.FiniteSubsetsInAffineOpens
theorem _root_.solution (f : X ⟶ Y) [IsImmersion f] [FiniteSubsetsInAffineOpens Y] :
    FiniteSubsetsInAffineOpens X :=
  of_isAffineHom (Y := f.coborderRange.toScheme) f.liftCoborder
end GlobalTheory.FiniteSubsetsInAffineOpens
