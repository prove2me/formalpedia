-- Prove2me | solution 1 for GlobalTheory.flat_of_tame_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:50.149273+00:00
-- url     : https://prove2.me/submissions/a62e0fda-1a63-482b-8a73-8d144732bb6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent
import Theorems.Thm_GlobalTheory_TameFlat_flat_of_retraction
import Theorems.Thm_GlobalTheory_TameFlat_exists_retraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R]
      [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R]
      [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C]
      [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ]
      [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) →
      Function.Injective (algebraMap R C) →
      (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) →
      Algebra.IsPushout A B R C → Module.Flat B C → (∃ b : B, ∑ᶠ g : Γ, g • b = 1) →
      Module.Flat A R := by
  intro Γ _ _ A B R C
  intros
  rename_i hAB _ _ hpo hflat htr
  obtain ⟨b, hb⟩ := htr
  obtain ⟨e, he⟩ := TameFlat.exists_retraction (Γ := Γ) (A := A) hAB b hb
  have : Module.Flat B (B ⊗[A] R) := Module.Flat.of_linearEquiv hpo.out.equiv
  exact TameFlat.flat_of_retraction e he
end GlobalTheory
