-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:04.933716+00:00
-- url     : https://prove2.me/submissions/9c7594c8-3b31-45d5-b3f1-f4f462d3c5dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Theorems.Thm_GlobalTheory_isIso_fromNormalization_of_birational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsOpenImmersion f := by
  obtain ⟨U, hU, hpre⟩ := f.exists_isIso_morphismRestrict_toNormalization
  have hsurj : Function.Surjective (f.toNormalization ⁻¹ᵁ U).ι := by
    intro x
    have hx : x ∈ f.toNormalization ⁻¹ᵁ U := by
      show x ∈ (f.toNormalization ⁻¹ᵁ U).carrier
      rw [hpre]
      exact f.quasiFiniteAt x
    exact ⟨⟨x, hx⟩, rfl⟩
  haveI : IsIso (f.toNormalization ⁻¹ᵁ U).ι := by
    rw [isIso_iff_isOpenImmersion_and_epi_base, TopCat.epi_iff_surjective]
    exact ⟨inferInstance, hsurj⟩
  have h1 : IsOpenImmersion ((f.toNormalization ⁻¹ᵁ U).ι ≫ f.toNormalization) := by
    rw [← morphismRestrict_ι]
    infer_instance
  haveI : IsOpenImmersion f.toNormalization :=
    (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion _ _).mp h1
  haveI := _root_.GlobalTheory.isIso_fromNormalization_of_birational f hY
  rw [← f.toNormalization_fromNormalization]
  infer_instance
end _root_.GlobalTheory
end GlobalTheory
