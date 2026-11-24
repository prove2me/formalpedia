-- Prove2me | solution 1 for GlobalTheory.OrbitsInAffineOpens.of_isQProjOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:38:59.902524+00:00
-- url     : https://prove2.me/submissions/28c26221-9ac2-4618-86d1-ad9a7d2e883e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_FiniteSubsetsInAffineOpens_of_isQProjOver

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
open GlobalTheory.OrbitsInAffineOpens
namespace GlobalTheory.OrbitsInAffineOpens
theorem _root_.solution [Finite G] {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f)
    (ρ : G →* Aut X) : OrbitsInAffineOpens ρ := by
  have := FiniteSubsetsInAffineOpens.of_isQProjOver h
  infer_instance
end GlobalTheory.OrbitsInAffineOpens
