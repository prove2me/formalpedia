-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:56.765903+00:00
-- url     : https://prove2.me/submissions/f9c32f6d-a98c-44d1-8c09-f27ec497d995

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FinitelyManyOpenSubgroupsBoundedIndex
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_iff_le_maxUnramifiedOutside


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GlobalFiniteness
namespace GlobalTheory.CompanionTheory.GlobalFiniteness
theorem _root_.solution :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Set (HeightOneSpectrum (𝓞 F))),
      (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
        Module.finrank F E ≤ N}.Finite) →
      ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) |
        IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S hfin N
  haveI : IsGalois F Ω := IsSepClosure.isGalois
  let K := maxUnramifiedOutside F Ω S
  let φ : Subgroup (galUnramifiedOutside F Ω S) → IntermediateField F Ω :=
    fun H => IntermediateField.lift (F := K) (IntermediateField.fixedField (H : Subgroup Gal(K/F)))
  have key : ∀ H : Subgroup Gal(K/F), IsOpen (H : Set Gal(K/F)) →
      (IntermediateField.fixedField H).fixingSubgroup = H := fun H hH =>
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
  apply Set.Finite.of_finite_image (f := φ)
  · apply (hfin N).subset
    rintro _ ⟨H, ⟨hHo, -, hHN⟩, rfl⟩
    have hfix := key H hHo
    have hfd : FiniteDimensional F (IntermediateField.fixedField (H : Subgroup Gal(K/F))) :=
      (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hHo)
    let e : (IntermediateField.fixedField (H : Subgroup Gal(K/F))) ≃ₐ[F] (φ H) :=
      IntermediateField.equivMap _ (IntermediateField.val K)
    haveI : FiniteDimensional F (φ H) := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine ⟨inferInstance, (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2
      (IntermediateField.lift_le _), ?_⟩
    rw [← e.toLinearEquiv.finrank_eq, IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact hHN
  · intro H₁ h₁ H₂ h₂ h
    have h' := IntermediateField.lift_injective K h
    exact (key H₁ h₁.1).symm.trans ((congrArg IntermediateField.fixingSubgroup h').trans (key H₂ h₂.1))
end GlobalTheory.CompanionTheory.GlobalFiniteness
