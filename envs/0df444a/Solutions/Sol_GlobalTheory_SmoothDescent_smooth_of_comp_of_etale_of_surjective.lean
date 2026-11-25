-- Prove2me | solution 1 for GlobalTheory.SmoothDescent.smooth_of_comp_of_etale_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:19.511444+00:00
-- url     : https://prove2.me/submissions/71d82a55-b9d3-45e7-89f4-42b03135af59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionDescendsEtaleCover
import Theorems.Thm_GlobalTheory_SmoothDescent_formallySmooth_of_faithfullyFlat
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_faithfullyFlat_stalkMap_of_flat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmoothDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.SmoothDescent
theorem _root_.solution {X Y S : Scheme.{0}} (π : X ⟶ Y) (s : Y ⟶ S)
    [IsLocallyNoetherian S] [Etale π] [Surjective π] [LocallyOfFiniteType s] [Smooth (π ≫ s)] :
    Smooth s := by
  have : LocallyOfFinitePresentation s := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have : Flat π := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale π›).1
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := π.surjective y
  rw [Scheme.Hom.mem_smoothLocus]
  have h : ((π ≫ s).stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((π ≫ s).smoothLocus_eq_top.ge (Set.mem_univ x))
  rw [Scheme.Hom.stalkMap_comp] at h
  replace h : ((π.stalkMap x).hom.comp (s.stalkMap (π x)).hom).FormallySmooth := h
  have hs : (π.stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (π.smoothLocus_eq_top.ge (Set.mem_univ x))
  have hu := FormallyUnramified.stalkMap π x
  have hf := faithfullyFlat_stalkMap_of_flat π x
  have e₁ := LocallyOfFiniteType.stalkMap π x
  have e₂ := LocallyOfFiniteType.stalkMap s (π x)
  algebraize [(π.stalkMap x).hom, (s.stalkMap (π x)).hom, (π.stalkMap x).hom.comp (s.stalkMap (π x)).hom]
  have : Algebra.FormallyEtale (Y.presheaf.stalk (π x)) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  exact formallySmooth_of_faithfullyFlat (S.presheaf.stalk (s (π x))) (Y.presheaf.stalk (π x))
    (X.presheaf.stalk x)
end GlobalTheory.SmoothDescent
