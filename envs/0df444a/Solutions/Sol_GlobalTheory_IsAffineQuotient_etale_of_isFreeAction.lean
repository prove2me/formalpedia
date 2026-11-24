-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.etale_of_isFreeAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:38.840952+00:00
-- url     : https://prove2.me/submissions/f0bfbc8c-20ee-4e05-a42f-3ceb52e8479c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsFreeAction_isFreeRingAction
import Theorems.Thm_GlobalTheory_FreeQuotient_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
open GlobalTheory.IsAffineQuotient
variable [Finite G] {ρ : G →* Aut X} {π : X ⟶ Y} (h : IsAffineQuotient ρ π) (hρ : IsFreeAction ρ)
include h hρ
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution : Etale π := by
  have := h.isAffineHom
  refine (HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      fun R S _ _ _ r _ ↦ RingHom.etale_algebraMap.mpr (.of_isLocalizationAway r)).1).mpr fun x ↦ ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π x)) isOpen_univ
  have hW : IsAffineOpen W := hW
  refine ⟨⟨W, hW⟩, ⟨_, hW.preimage π⟩, hy, le_rfl, ?_⟩
  let := sectionsAction ρ _ (h.preimage_le W)
  let := (π.app W).hom.toAlgebra
  obtain ⟨_, _, _⟩ := h.isInvariant W
  rw [Scheme.Hom.appLE_eq_app]
  exact FreeQuotient.etale Γ(Y, W) (hρ.isFreeRingAction (hW.preimage π) (h.preimage_le W))
end GlobalTheory.IsAffineQuotient
