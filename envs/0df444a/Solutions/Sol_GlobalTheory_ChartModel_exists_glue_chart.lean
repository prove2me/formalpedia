-- Prove2me | solution 1 for GlobalTheory.ChartModel.exists_glue_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:34.098363+00:00
-- url     : https://prove2.me/submissions/8bdc1db3-3534-46dc-a95d-68082fe9fe97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChart
import Theorems.Thm_GlobalTheory_ChartModel_isSeparated_of_two
import Theorems.Thm_GlobalTheory_GlueModels_isOpenImmersion_inl
import Theorems.Thm_GlobalTheory_GlueModels_isOpenImmersion_inr
import Theorems.Thm_GlobalTheory_GlueModels_pushout_cover


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
open GlobalTheory GlobalTheory.ChartModel
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.ChartModel
theorem _root_.solution {S T A X W : Scheme.{0}} (i : T ⟶ S) [IsOpenImmersion i] (a : A ⟶ T) (c : X ⟶ S)
    {p : W ⟶ X} {w : W ⟶ T} (hW : IsPullback p w c i) (u : W ⟶ A) [IsOpenImmersion u] (hu : u ≫ a = w)
    [Smooth a] [IsSeparated a] [Smooth c] [IsSeparated c] [CompactSpace A] [CompactSpace X] :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (g : X ⟶ Y) (j : A ⟶ Y), IsOpenImmersion g ∧ IsPullback j a f i ∧ g ≫ f = c ∧
      p ≫ g = u ≫ j ∧ Smooth f ∧ IsSeparated f ∧ CompactSpace Y ∧ ∀ y, f y ∉ Set.range i → y ∈ Set.range g := by
  have : IsOpenImmersion p := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hW.flip ‹_›
  have := GlueModels.isOpenImmersion_inl p u
  have := GlueModels.isOpenImmersion_inr p u
  have hc := GlueModels.pushout_cover p u
  let f : pushout p u ⟶ S := pushout.desc c (a ≫ i) (by rw [hW.w, ← Category.assoc, hu])
  have h1 : pushout.inl p u ≫ f = c := pushout.inl_desc _ _ _
  have h2 : pushout.inr p u ≫ f = a ≫ i := pushout.inr_desc _ _ _
  have e1 (x : X) : f (pushout.inl p u x) = c x := congrArg (fun g => g x) h1
  have e2 (x : A) : f (pushout.inr p u x) = i (a x) := congrArg (fun g => g x) h2
  have e3 (x : W) : pushout.inl p u (p x) = pushout.inr p u (u x) :=
    congrArg (fun g => g x) (pushout.condition (f := p) (g := u))
  have hin (y) (hy : f y ∈ Set.range i) : y ∈ Set.range (pushout.inr p u) := by
    rcases hc y with ⟨x, rfl⟩ | hy
    · obtain ⟨t, ht⟩ := hy
      obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hW x t ((e1 x).symm.trans ht.symm)
      exact ⟨u z, (e3 z).symm⟩
    · exact hy
  have hout (y) (hy : f y ∉ Set.range i) : y ∈ Set.range (pushout.inl p u) := by
    rcases hc y with h | ⟨x, rfl⟩
    · exact h
    · exact absurd ⟨a x, (e2 x).symm⟩ hy
  refine ⟨_, f, pushout.inl p u, pushout.inr p u, inferInstance, ?_, h1, pushout.condition, ?_, ?_, ?_, hout⟩
  · refine (IsOpenImmersion.isPullback _ _ _ _ h2 ?_).flip
    ext y
    constructor
    · exact hin y
    · rintro ⟨x, rfl⟩
      exact ⟨a x, (e2 x).symm⟩
  · refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (twoCover _ _ hc) ?_
    rintro (_ | _)
    · change Smooth (pushout.inl p u ≫ f)
      rw [h1]; infer_instance
    · change Smooth (pushout.inr p u ≫ f)
      rw [h2]; infer_instance
  · have : IsSeparated (pushout.inl p u ≫ f) := by rw [h1]; infer_instance
    have : IsSeparated (pushout.inr p u ≫ f) := by rw [h2]; infer_instance
    refine isSeparated_of_two (pushout.inl p u) (pushout.inr p u) f fun x y hxy => ?_
    by_cases hx : f x ∈ Set.range i
    · exact Or.inr ⟨hin x hx, hin y (hxy ▸ hx)⟩
    · exact Or.inl ⟨hout x hx, hout y (hxy ▸ hx)⟩
  · refine ⟨?_⟩
    rw [← Set.eq_univ_of_forall (s := Set.range (pushout.inl p u) ∪ Set.range (pushout.inr p u)) hc]
    exact (isCompact_range (pushout.inl p u).continuous).union (isCompact_range (pushout.inr p u).continuous)
end GlobalTheory.ChartModel
