-- Prove2me | solution 1 for GlobalTheory.FiniteSubsetsInAffineOpens.of_isAffineHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:47:43.524997+00:00
-- url     : https://prove2.me/submissions/604b219b-b6f1-4412-8748-aa9110f7fb7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff

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
theorem _root_.solution (f : X ⟶ Y) [IsAffineHom f] [FiniteSubsetsInAffineOpens Y] :
    FiniteSubsetsInAffineOpens X := ⟨fun s hs ↦ by
  obtain ⟨V, hV, hsV⟩ := exists_isAffineOpen (X := Y) ((fun x : X ↦ f x) '' s) (hs.image _)
  exact ⟨f ⁻¹ᵁ V, hV.preimage f, fun x hx ↦ hsV ⟨x, hx, rfl⟩⟩⟩
end GlobalTheory.FiniteSubsetsInAffineOpens
