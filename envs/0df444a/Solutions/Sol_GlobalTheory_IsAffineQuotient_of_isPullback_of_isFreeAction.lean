-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.of_isPullback_of_isFreeAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:35.565349+00:00
-- url     : https://prove2.me/submissions/ed65a865-ff56-4898-87ee-465e74b2777b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsFreeAction_isFreeRingAction
import Theorems.Thm_GlobalTheory_IsAffineQuotient_of_isPullback_of_flat_or_sum_eq_one
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_FreeQuotient_exists_sum_smul_eq_one_of_free
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y X' Y' S S' : Scheme.{u}}
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
open GlobalTheory.IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y} (h : IsAffineQuotient ρ π)
  {ρ' : G →* Aut X'} {π' : X' ⟶ Y'} {p : X' ⟶ X} {t : Y' ⟶ Y} (H : IsPullback p π' π t)
  (hp : ∀ g, (ρ' g).hom ≫ p = p ≫ (ρ g).hom) (hπ' : ∀ g, (ρ' g).hom ≫ π' = π')
include h H hp hπ'
variable [Finite G]
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution (hρ : IsFreeAction ρ) : IsAffineQuotient ρ' π' :=
  have := Fintype.ofFinite G
  have := h.isAffineHom
  h.of_isPullback_of_flat_or_sum_eq_one H hp hπ' fun W hW _ _ _ ↦ .inr <|
    letI := sectionsAction ρ _ (h.preimage_le W)
    FreeQuotient.exists_sum_smul_eq_one_of_free
      (hρ.isFreeRingAction (hW.preimage π) (h.preimage_le W))
end GlobalTheory.IsAffineQuotient
