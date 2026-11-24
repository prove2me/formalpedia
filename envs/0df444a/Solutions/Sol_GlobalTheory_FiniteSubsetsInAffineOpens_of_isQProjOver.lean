-- Prove2me | solution 1 for GlobalTheory.FiniteSubsetsInAffineOpens.of_isQProjOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:24.316553+00:00
-- url     : https://prove2.me/submissions/a225e078-0116-4a06-8345-2d2d1f536214

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
    {f : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f) :
    FiniteSubsetsInAffineOpens X := by
  obtain ⟨N, i, hi, -, -⟩ := h
  exact of_isImmersion i
end GlobalTheory.FiniteSubsetsInAffineOpens
