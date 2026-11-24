-- Prove2me | solution 1 for GlobalTheory.smooth_of_isPullback_of_surjective_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:46.288276+00:00
-- url     : https://prove2.me/submissions/5fd52cd3-a9a5-4f53-89fb-2f087698b07d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfIsPullbackOfSurjectiveOfFlat

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X X' Y Y' : Scheme.{0}) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), IsPullback φ p p' π → Surjective π → Flat p' → LocallyOfFinitePresentation p' → Smooth p → Smooth p' := by
  intro X X' Y Y' π φ p p' h hπ hflat hlfp hsm

  refine Smooth.of_smooth_fiberToSpecResidueField p' fun y' => ?_

  obtain ⟨y, rfl⟩ := hπ.surj y'

  have hsq := (isPullback_fiberToSpecResidueField_of_isPullback h y).flip

  have hff : (π.residueFieldMap y).hom.FaithfullyFlat := by
    letI := (π.residueFieldMap y).hom.toAlgebra
    show Module.FaithfullyFlat _ _
    infer_instance
  obtain ⟨hF, hS⟩ := (flat_and_surjective_SpecMap_iff _).2 hff

  have hfib : Smooth (p.fiberToSpecResidueField y) :=
    inferInstanceAs (Smooth (pullback.snd p (X.fromSpecResidueField y)))

  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq ⟨⟨hS, hF⟩, inferInstance⟩ hfib
end GlobalTheory
