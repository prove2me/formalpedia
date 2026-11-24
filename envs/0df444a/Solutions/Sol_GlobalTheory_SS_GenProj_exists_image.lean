-- Prove2me | solution 1 for GlobalTheory.SS.GenProj.exists_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:16:46.8915+00:00
-- url     : https://prove2.me/submissions/ddca36d0-b51e-466f-91de-a7257c9b49ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GenProj
namespace GlobalTheory.SS.GenProj
theorem _root_.solution {U X : Scheme.{0}} (p : U ⟶ X) [Flat p] [LocallyOfFinitePresentation p] :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme), p' ≫ V.ι = p ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' := by
  let V : X.Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  have hr : Set.range p ⊆ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact subset_rfl
  have e : IsOpenImmersion.lift V.ι p hr ≫ V.ι = p := IsOpenImmersion.lift_fac _ _ _
  have hP : IsPullback (IsOpenImmersion.lift V.ι p hr) (𝟙 U) V.ι p :=
    IsPullback.of_vert_isIso_mono ⟨by rw [e, Category.id_comp]⟩
  refine ⟨V, IsOpenImmersion.lift V.ι p hr, e, ?_, ?_, ⟨?_⟩⟩
  · exact MorphismProperty.of_isPullback (P := @Flat) hP.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hP.flip ‹_›
  · rintro ⟨_, u, rfl⟩
    refine ⟨u, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, e]; rfl
end GlobalTheory.SS.GenProj
