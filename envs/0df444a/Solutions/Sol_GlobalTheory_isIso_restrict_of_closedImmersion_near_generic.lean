-- Prove2me | solution 1 for GlobalTheory.isIso_restrict_of_closedImmersion_near_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:41.714817+00:00
-- url     : https://prove2.me/submissions/6f255d34-69b5-44ed-8d94-6bc3cd86a749

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoRestrictOfClosedImmersionNearGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W)
      (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ →
      i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) →
      ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by
  intro W W' Y Y₁ _ _ i _ h c _ s₁ U hiso hcomm hη hw
  obtain ⟨w', hw'⟩ := hw
  refine ⟨i ⁻¹ᵁ U, ⟨genericPoint W, hη⟩, ?_⟩
  have hi : IsClosedImmersion (i ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› U
  have hc : IsClosedImmersion (c ∣_ (s₁ ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› _
  have h1 : IsClosedImmersion ((c ≫ s₁) ∣_ U) := by
    rw [morphismRestrict_comp]
    have hs : IsClosedImmersion (s₁ ∣_ U) := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hc hs
  have h2 : IsClosedImmersion ((h ≫ i) ∣_ U) := by
    rw [hcomm]; exact h1
  rw [morphismRestrict_comp] at h2
  have h3 : IsClosedImmersion (h ∣_ (i ⁻¹ᵁ U)) :=
    @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ (i ∣_ U) hi h2
  have hw'U : w' ∈ h ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    show h w' ∈ i ⁻¹ᵁ U
    rw [hw']; exact hη
  have h4 : Surjective (h ∣_ (i ⁻¹ᵁ U)) := by
    constructor
    intro x
    have hcl : IsClosed (Set.range (h ∣_ (i ⁻¹ᵁ U))) := (h ∣_ (i ⁻¹ᵁ U)).isClosedEmbedding.isClosed_range
    let p : (h ⁻¹ᵁ (i ⁻¹ᵁ U) : Scheme) := ⟨w', hw'U⟩
    have hp : ((h ∣_ (i ⁻¹ᵁ U)) p).1 = genericPoint W := by
      rw [morphismRestrict_base_coe]; exact hw'
    have hsp : (h ∣_ (i ⁻¹ᵁ U)) p ⤳ x := by
      rw [← (i ⁻¹ᵁ U).ι.isOpenEmbedding.toIsInducing.specializes_iff]
      have : (i ⁻¹ᵁ U).ι ((h ∣_ (i ⁻¹ᵁ U)) p) = genericPoint W := hp
      rw [this]
      exact (genericPoint_spec W).specializes (Set.mem_univ _)
    exact hsp.mem_closed hcl ⟨p, rfl⟩
  exact isIso_of_isClosedImmersion_of_surjective _
end GlobalTheory
