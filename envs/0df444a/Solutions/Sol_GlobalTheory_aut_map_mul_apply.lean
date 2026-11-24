-- Prove2me | solution 1 for GlobalTheory.aut_map_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:18.293541+00:00
-- url     : https://prove2.me/submissions/33c20f2c-fef7-4e27-8ee0-a5aad0920a8d

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
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
variable {ρ : G →* Aut X}
namespace GlobalTheory
theorem _root_.solution (ρ : G →* Aut X) (g k : G) (x : X) :
    (ρ (g * k)).hom x = (ρ g).hom ((ρ k).hom x) := by
  rw [map_mul, Aut.Aut_mul_def]
  exact Scheme.Hom.comp_apply (ρ k).hom (ρ g).hom x
end GlobalTheory
