-- Prove2me | solution 1 for GlobalTheory.SS.TorusSlice.isOpenImmersion_of_flat_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:14.219784+00:00
-- url     : https://prove2.me/submissions/c13ef53a-c218-47ee-90ba-fa848bdfcbbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorusSlice
namespace GlobalTheory.SS.TorusSlice
theorem _root_.solution {W A P G : Scheme.{0}} {q : W ⟶ P} {p : W ⟶ A} {a : P ⟶ G} {m : A ⟶ G}
    (h : IsPullback q p a m) [IsOpenImmersion p] [Flat m] [LocallyOfFinitePresentation m] [QuasiCompact m]
    (hr : Set.range a ⊆ Set.range m) : IsOpenImmersion a := by
  let U : G.Opens := ⟨Set.range m, m.isOpenMap.isOpen_range⟩
  have hU : Set.range U.ι = Set.range m := U.range_ι
  let m' := IsOpenImmersion.lift U.ι m hU.ge
  let a' := IsOpenImmersion.lift U.ι a (hr.trans hU.ge)
  have em : m' ≫ U.ι = m := IsOpenImmersion.lift_fac _ _ _
  have ea : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hm : IsPullback m' (𝟙 _) U.ι m := IsPullback.of_vert_isIso_mono ⟨em.trans (Category.id_comp _).symm⟩
  have hs : Surjective m' := ⟨fun u => by
    obtain ⟨y, hy⟩ := u.2
    refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, em]; exact hy⟩
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) m' :=
    ⟨⟨hs, MorphismProperty.of_isPullback hm.flip ‹Flat m›⟩, MorphismProperty.of_isPullback hm.flip ‹QuasiCompact m›⟩
  have H : IsPullback q p a' m' := by
    refine ⟨⟨by rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ea, em, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => h.lift s.fst s.snd (by rw [← ea, ← em, s.condition_assoc])) (fun s => h.lift_fst _ _ _)
      (fun s => h.lift_snd _ _ _) fun s l h1 h2 => h.hom_ext ?_ ?_⟩⟩
    · rw [h1, h.lift_fst]
    · rw [h2, h.lift_snd]
  have : IsOpenImmersion a' := MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip hq ‹_›
  rw [← ea]; infer_instance
end GlobalTheory.SS.TorusSlice
