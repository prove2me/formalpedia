-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.orbitsInAffineOpens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:14.857918+00:00
-- url     : https://prove2.me/submissions/2cc65ea3-1dc8-49b3-a2ef-6ba4f02703fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_OrbitsInAffineOpens_of_invariant

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
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
namespace GlobalTheory
namespace IsAffineQuotient
theorem _root_.solution {ρ : G →* Aut X} {π : X ⟶ Y}
    (h : IsAffineQuotient ρ π) : OrbitsInAffineOpens ρ := by
  have := h.isAffineHom
  exact OrbitsInAffineOpens.of_invariant ρ π h.comp_eq
end IsAffineQuotient
end GlobalTheory
