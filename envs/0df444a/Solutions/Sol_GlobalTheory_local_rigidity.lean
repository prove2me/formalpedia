-- Prove2me | solution 1 for GlobalTheory.local_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:59.799081+00:00
-- url     : https://prove2.me/submissions/8bcb7249-20d4-4179-ae81-cbde39c8ad04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Theorems.Thm_GlobalTheory_eq_comp_section_of_surjective_appTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g := by
  intro X T Y p ε g h hp hsurj t y hfib
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have hZ : IsClosed (p '' (g ⁻¹ᵁ W : Set X)ᶜ) :=
    p.isClosedMap _ (g ⁻¹ᵁ W).isOpen.isClosed_compl
  let V : T.Opens := ⟨(p '' (g ⁻¹ᵁ W : Set X)ᶜ)ᶜ, hZ.isOpen_compl⟩
  have htV : t ∈ V := by
    rintro ⟨x, hx, rfl⟩
    exact hx (show g x ∈ W from (hfib x rfl).symm ▸ hyW)
  have hsub : p ⁻¹ᵁ V ≤ g ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩
  have hεV : V ≤ ε ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro s hs
    change p (ε s) ∈ V
    rw [← Scheme.Hom.comp_apply, h]
    exact hs
  haveI : IsAffine W := hW
  refine ⟨V, htV, ?_⟩
  have hsec : ε.resLE (p ⁻¹ᵁ V) V hεV ≫ p ∣_ V = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, h]
    simp
  have hsV : Function.Surjective (p ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    have hiso := ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)
    exact hiso.2.comp (hsurj (V.ι ''ᵁ ⊤))
  have key := congrArg (· ≫ W.ι)
    (_root_.GlobalTheory.eq_comp_section_of_surjective_appTop (p ∣_ V) (ε.resLE (p ⁻¹ᵁ V) V hεV)
      (g.resLE W (p ⁻¹ᵁ V) hsub) hsec hsV)
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι] at key
  rw [key, Scheme.Hom.resLE_comp_ι_assoc, ← Category.assoc (p ∣_ V), morphismRestrict_ι,
    Category.assoc]
end _root_.GlobalTheory
end GlobalTheory
