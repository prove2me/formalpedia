-- Prove2me | solution 1 for GlobalTheory.FiniteBirationalNear.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:45:28.528447+00:00
-- url     : https://prove2.me/submissions/ffba9d52-2af5-40d7-a51a-0e7d35c338a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational
import Theorems.Thm_GlobalTheory_FiniteBirationalNear_exists_isIntegral_nhds
import Theorems.Thm_GlobalTheory_FiniteBirationalNear_exists_isIso_of_isIntegral
import Theorems.Thm_GlobalTheory_birational_of_isIso_morphismRestrict


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.FiniteBirationalNear
namespace GlobalTheory.FiniteBirationalNear
theorem _root_.solution : ∀ (U M : Scheme.{0}) [IsLocallyNoetherian M] (u : U ⟶ M) (W : M.Opens), IsFinite u → IsReduced U → IsIso (u ∣_ W) → Dense (W : Set M) → Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) → ∀ x : M, IsDomain (M.presheaf.stalk x) → IsIntegrallyClosed (M.presheaf.stalk x) → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V) := by
  intro U M _ u W _ _ hW hd hd' x _ _
  obtain ⟨V, hxV, hV⟩ := exists_isIntegral_nhds x
  let f := u ∣_ V
  let W' : V.toScheme.Opens := V.ι ⁻¹ᵁ W
  have : IsFinite f := MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback_morphismRestrict u V).flip ‹_›
  have hW' : IsIso (f ∣_ W') := by
    have h1 : IsIso (u ∣_ W ∣_ (W.ι ⁻¹ᵁ V)) := inferInstance
    have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u W (W.ι ⁻¹ᵁ V))).1 h1
    have e : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V.ι ''ᵁ W' := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u V W')).2
      (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq u e)).1 h2)
  have hne : Nonempty W' := by
    obtain ⟨z, hz, hz'⟩ := hd.inter_open_nonempty V V.isOpen ⟨x, hxV⟩
    exact ⟨⟨⟨z, hz⟩, hz'⟩⟩
  have : IsIntegral W' := isIntegral_of_isOpenImmersion W'.ι
  have : IsIntegral (f ⁻¹ᵁ W') := IsIntegral.of_isIso (inv (f ∣_ W'))
  have hd₂ : Dense ((f ⁻¹ᵁ W' : (u ⁻¹ᵁ V).toScheme.Opens) : Set (u ⁻¹ᵁ V).toScheme) := by
    have e : f ⁻¹ᵁ W' = (u ⁻¹ᵁ V).ι ⁻¹ᵁ u ⁻¹ᵁ W := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
    rw [e]
    exact hd'.preimage (u ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap
  have : IrreducibleSpace (u ⁻¹ᵁ V).toScheme := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hd₂.closure_eq]
    refine IsIrreducible.closure ?_
    exact isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace (f ⁻¹ᵁ W').toScheme))
  have : IsIntegral (u ⁻¹ᵁ V).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict f W' hne
  have : IsIntegrallyClosed (V.toScheme.presheaf.stalk (⟨x, hxV⟩ : V)) :=
    IsIntegrallyClosed.of_equiv (R := M.presheaf.stalk x)
      (V.stalkIso ⟨x, hxV⟩).symm.commRingCatIsoToRingEquiv
  obtain ⟨V', hx', hV'⟩ := exists_isIso_of_isIntegral f ⟨x, hxV⟩
  refine ⟨V.ι ''ᵁ V', ⟨⟨x, hxV⟩, hx', rfl⟩, ?_⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict u V V')).1 hV'
end GlobalTheory.FiniteBirationalNear
