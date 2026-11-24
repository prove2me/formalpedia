-- Prove2me | solution 1 for GlobalTheory.exists_isInvariantSection_basicOpen_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:41.128834+00:00
-- url     : https://prove2.me/submissions/f35e7e23-f6ed-439a-be69-425bef18bf08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_aut_map_one_apply
import Theorems.Thm_GlobalTheory_exists_isInvariantSection_mem_basicOpen_iff

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
variable [Finite G]
namespace GlobalTheory
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U)
    (hst : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) {x : X} (hx : x ∈ U) (O : X.Opens)
    (hO : ∀ g, (ρ g).hom x ∈ O) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧ x ∈ X.basicOpen t ∧ X.basicOpen t ≤ O := by
  obtain ⟨f, hsf, hfO⟩ := exists_basicOpen_le_of_finite hU O (Set.finite_range fun g ↦ (ρ g).hom x)
    (by rintro _ ⟨g, rfl⟩; exact hst g hx) (by rintro _ ⟨g, rfl⟩; exact hO g)
  obtain ⟨t, ht, hmem⟩ := exists_isInvariantSection_mem_basicOpen_iff hst f
  refine ⟨t, ht, (hmem x).2 fun g ↦ hsf ⟨g, rfl⟩, fun y hy ↦ hfO ?_⟩
  have := (hmem y).1 hy 1
  rwa [aut_map_one_apply] at this
end GlobalTheory
