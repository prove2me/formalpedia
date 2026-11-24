-- Prove2me | solution 1 for GlobalTheory.SS.FinUnion.exists_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:53:37.814906+00:00
-- url     : https://prove2.me/submissions/39131b28-6365-4c32-a92e-50a64568cd99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FinUnion
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.FinUnion
theorem _root_.solution {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (O : (pullback f g).Opens) (z₀ : ↥(pullback f g))
    (h₀ : z₀ ∈ O) (V : X.Opens) (hirr : IsPreirreducible (f ⁻¹' {g (pullback.snd f g z₀)}))
    (x : X) (hx : x ∈ V) (hx' : f x = g (pullback.snd f g z₀)) :
    ∃ z ∈ O, pullback.snd f g z = pullback.snd f g z₀ ∧ pullback.fst f g z ∈ V := by
  set y := pullback.snd f g z₀ with hy
  have H0 : IsPullback ((pullback.snd f g).fiberι y) ((pullback.snd f g).fiberToSpecResidueField y)
      (pullback.snd f g) (Y.fromSpecResidueField y) := IsPullback.of_hasPullback _ _
  have H1 := H0.paste_horiz (IsPullback.of_hasPullback f g)
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at H1
  have H2 : IsPullback (f.fiberι (g y)) (f.fiberToSpecResidueField (g y)) f (S.fromSpecResidueField (g y)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨p, hp1, hp2⟩ := H2.exists_lift ((pullback.snd f g).fiberι y ≫ pullback.fst f g)
    ((pullback.snd f g).fiberToSpecResidueField y ≫ Spec.map (g.residueFieldMap y)) (by
      rw [H1.w, Category.assoc])
  rw [← hp1] at H1
  have H3 := H1.of_right hp2 H2
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback H3.flip inferInstance
  have hp : ∀ w, f.fiberι (g y) (p w) = pullback.fst f g ((pullback.snd f g).fiberι y w) := fun w => by
    rw [← Scheme.Hom.comp_apply, hp1, Scheme.Hom.comp_apply]
  obtain ⟨w₀, hw₀⟩ : z₀ ∈ Set.range ((pullback.snd f g).fiberι y) := by
    rw [Scheme.Hom.range_fiberι]; rfl
  obtain ⟨x₀, hx₀⟩ : x ∈ Set.range (f.fiberι (g y)) := by
    rw [Scheme.Hom.range_fiberι]; exact hx'
  have hI : IsPreirreducible (Set.univ : Set (f.fiber (g y))) := by
    have := Subtype.preirreducibleSpace hirr
    have h := (PreirreducibleSpace.isPreirreducible_univ (X := f ⁻¹' {g y})).image _
      (f.fiberHomeo (g y)).symm.continuous.continuousOn
    rwa [Set.image_univ, (f.fiberHomeo (g y)).symm.surjective.range_eq] at h
  obtain ⟨_, -, ⟨w, hw, rfl⟩, hV⟩ := hI _ _
    (p.isOpenMap _ (O.isOpen.preimage ((pullback.snd f g).fiberι y).continuous))
    (V.isOpen.preimage (f.fiberι (g y)).continuous) ⟨p w₀, trivial, w₀, by simpa [hw₀] using h₀, rfl⟩
    ⟨x₀, trivial, by simpa [hx₀] using hx⟩
  refine ⟨_, hw, ((pullback.snd f g).range_fiberι y).le ⟨w, rfl⟩, ?_⟩
  rw [← hp]; exact hV
end GlobalTheory.SS.FinUnion
