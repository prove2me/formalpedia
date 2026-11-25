-- Prove2me | solution 1 for GlobalTheory.T.exists_descent_of_morphisms_to_subfield
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:07:25.73641+00:00
-- url     : https://prove2.me/submissions/3715bf6b-21a7-436e-8567-e903f205bf8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsDescendToLargeSubfield
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsDescendToLargeSubfieldStatement
import Theorems.Thm_GlobalTheory_morphisms_descend_to_large_subfield


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  first | exact @GlobalTheory.morphisms_descend_to_large_subfield | exact GlobalTheory.morphisms_descend_to_large_subfield | (intros; apply GlobalTheory.morphisms_descend_to_large_subfield <;> assumption)
end _root_.GlobalTheory.T
