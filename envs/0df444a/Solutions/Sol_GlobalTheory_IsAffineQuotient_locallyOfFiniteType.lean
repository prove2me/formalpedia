-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:51.099387+00:00
-- url     : https://prove2.me/submissions/70915741-e188-4e1a-b054-08cbd63cf9f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_finiteType_of_isInvariant
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
variable {G : Type v} [Group G] {X Y Z : Scheme.{u}}
open GlobalTheory.IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y}
variable (h : IsAffineQuotient ρ π)
include h
variable [Finite G]
variable {S : Scheme.{u}} (q : Y ⟶ S)
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution [IsLocallyNoetherian S] [LocallyOfFiniteType (π ≫ q)] :
    LocallyOfFiniteType q := by
  have := h.isAffineHom
  refine (HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)).mpr fun U W e ↦ ?_
  have hf := HasRingHomProperty.appLE @LocallyOfFiniteType (π ≫ q) ‹_› U
    ⟨π ⁻¹ᵁ W, W.2.preimage π⟩ (π.preimage_mono e)
  let := sectionsAction ρ _ (h.preimage_le W)
  let := (π.app W).hom.toAlgebra
  obtain ⟨_, _, _⟩ := h.isInvariant W
  let := (q.appLE U W e).hom.toAlgebra
  let := ((π ≫ q).appLE U (π ⁻¹ᵁ W) (π.preimage_mono e)).hom.toAlgebra
  have : IsScalarTower Γ(S, U) Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := .of_algebraMap_eq' (by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE])
  have : Algebra.FiniteType Γ(S, U) Γ(X, π ⁻¹ᵁ W) := hf
  have := IsLocallyNoetherian.component_noetherian U
  exact finiteType_of_isInvariant Γ(X, π ⁻¹ᵁ W) G Γ(S, U) Γ(Y, W)
end GlobalTheory.IsAffineQuotient
