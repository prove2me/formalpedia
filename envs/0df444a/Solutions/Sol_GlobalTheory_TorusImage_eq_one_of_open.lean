-- Prove2me | solution 1 for GlobalTheory.TorusImage.eq_one_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:59.543863+00:00
-- url     : https://prove2.me/submissions/9f71e52f-013b-42ea-8815-d7dbe99d6b07

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
import Theorems.Thm_GlobalTheory_FlatQuotient_epi_of_flat_surjective
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.TorusImage
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
namespace GlobalTheory.TorusImage
theorem _root_.solution [Flat G.hom] [GeometricallyIrreducible G.hom] (U : G.left.Opens)
    (hU : ∀ s : S, ∃ y ∈ U, G.hom y = s) {Z : Over S} (x : Z ⟶ G)
    (h : ∀ (Y : Over S) (π : Y ⟶ Z) (g : Y ⟶ G), ⊤ ≤ ((π ≫ x) * g).left ⁻¹ᵁ U → ⊤ ≤ g.left ⁻¹ᵁ U → (π ≫ x) * g = g) :
    x = 1 := by
  let a : Z ⊗ G ⟶ G := (fst Z G ≫ x) * snd Z G
  let O : (Z ⊗ G).left.Opens := a.left ⁻¹ᵁ U ⊓ (snd Z G).left ⁻¹ᵁ U
  let Y : Over S := Over.mk (O.ι ≫ (Z ⊗ G).hom)
  let j : Y ⟶ Z ⊗ G := Over.homMk O.ι rfl
  have e1 : ((j ≫ fst Z G) ≫ x) * (j ≫ snd Z G) = j ≫ a := by
    rw [MonObj.comp_mul, Category.assoc]
  have h1 := h Y (j ≫ fst Z G) (j ≫ snd Z G) (by rw [e1]; exact fun y _ => y.2.1) (fun y _ => y.2.2)
  have h2 : (j ≫ fst Z G) ≫ x = (j ≫ fst Z G) ≫ 1 := by
    rw [MonObj.comp_one]; exact mul_eq_right.1 h1
  have hf : Flat (fst Z G).left := inferInstanceAs (Flat (pullback.fst Z.hom G.hom))
  have hg : GeometricallyIrreducible (fst Z G).left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst Z.hom G.hom))
  have : Flat (j ≫ fst Z G).left := inferInstanceAs (Flat (O.ι ≫ (fst Z G).left))
  have m2 : ∀ z : Z.left, ∃ w : (Z ⊗ G).left, (snd Z G).left w ∈ U ∧ (fst Z G).left w = z := by
    intro z
    obtain ⟨y, hy, e⟩ := hU (Z.hom z)
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z y e.symm
    exact ⟨w, by rw [← hw2] at hy; exact hy, hw1⟩
  have m1 : ∀ z : Z.left, ∃ w : (Z ⊗ G).left, a.left w ∈ U ∧ (fst Z G).left w = z := by
    intro z
    obtain ⟨w, hw1, hw2⟩ := m2 z
    let b : Z ⊗ G ⟶ Z ⊗ G := lift (fst Z G) ((fst Z G ≫ x)⁻¹ * snd Z G)
    have b1 : b ≫ a = snd Z G := by
      simp [a, b, MonObj.comp_mul, ← Category.assoc]
    have b2 : b ≫ fst Z G = fst Z G := lift_fst _ _
    refine ⟨b.left w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b1]; exact hw1
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b2]; exact hw2
  have : Surjective (j ≫ fst Z G).left := ⟨fun z => by
    have hi : IsIrreducible ((fst Z G).left ⁻¹' {z}) := by
      rw [← (fst Z G).left.range_fiberι, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ ((fst Z G).left.fiberι z).continuous.continuousOn
    obtain ⟨w, hw, e⟩ := m1 z
    obtain ⟨w', hw', e'⟩ := m2 z
    obtain ⟨y, hy, k₁, k₂⟩ := hi.2 _ _ (a.left ⁻¹ᵁ U).2 ((snd Z G).left ⁻¹ᵁ U).2 ⟨w, e, hw⟩ ⟨w', e', hw'⟩
    exact ⟨⟨y, k₁, k₂⟩, hy⟩⟩
  have := FlatQuotient.epi_of_flat_surjective (j ≫ fst Z G)
  exact (cancel_epi _).1 h2
end GlobalTheory.TorusImage
