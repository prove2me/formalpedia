-- Prove2me | solution 1 for GlobalTheory.flatQuotient_iso_of_same_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:24.683066+00:00
-- url     : https://prove2.me/submissions/cf073959-3955-4ea8-8799-b8ade32a9eaf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Theorems.Thm_GlobalTheory_FlatQuotient_epi_of_flat_surjective
import Theorems.Thm_GlobalTheory_FlatQuotient_exists_desc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (G B B' T T' : Over S) [GrpObj G] [GrpObj B] [GrpObj B'] [GrpObj T]
      [GrpObj T'] (q : G ⟶ B) (i : T ⟶ G) (q' : G ⟶ B') (i' : T' ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsMonHom q' → IsMonHom i' → Flat q'.left →
      Surjective q'.left → QuasiCompact q'.left → IsPullback i' (toUnit _) q' (η[B']) →
      i' ≫ q = toUnit _ ≫ η[B] → i ≫ q' = toUnit _ ≫ η[B'] →
      ∃ β : B' ≅ B, IsMonHom β.hom ∧ q' ≫ β.hom = q := by
  intro S G B B' T T' _ _ _ _ _ q i q' i' hq _ hqf hqs hqc hk hq' _ hq'f hq's hq'c hk' h₁ h₂
  obtain ⟨β, -, hqβ⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q i q' hk h₂
  obtain ⟨β', hβ', hq'β'⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q' i' q hk' h₁
  have eq : Epi q := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective q
  have eq' : Epi q' := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective q'
  have e₁ : β ≫ β' = 𝟙 B := by
    rw [← cancel_epi q, reassoc_of% hqβ, hq'β', Category.comp_id]
  have e₂ : β' ≫ β = 𝟙 B' := by
    rw [← cancel_epi q', reassoc_of% hq'β', hqβ, Category.comp_id]
  exact ⟨⟨β', β, e₂, e₁⟩, hβ', hq'β'⟩
end _root_.GlobalTheory
end GlobalTheory
