-- Prove2me | solution 1 for GlobalTheory.FiniteSubsetsInAffineOpens.of_isProjOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:43.569338+00:00
-- url     : https://prove2.me/submissions/fc1fa816-2af2-4afb-93de-11c1e4cd364a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_FiniteSubsetsInAffineOpens_of_isImmersion

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
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) :
    FiniteSubsetsInAffineOpens X := by
  obtain ⟨N, i, hi, -⟩ := h
  exact of_isImmersion i
end GlobalTheory.FiniteSubsetsInAffineOpens
