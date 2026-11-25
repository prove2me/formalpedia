-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.isPullback_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:43:33.433713+00:00
-- url     : https://prove2.me/submissions/5520a7a7-9c8f-4ea0-ae20-b744045e6783

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_GlobalTheory_ZJ_AddExt_isPullback_a

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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution (C : Core) (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left) (h : IsSquare C.a φ₂) :
    IsPullback φ₂ (C.A ⊗ C.A).hom (C.GG ⊗ C.GG).hom C.U.ι := by
  have hA := isPullback_a C
  have : IsOpenImmersion C.a := MorphismProperty.of_isPullback hA.flip inferInstance
  have w₁ : (fst C.GG C.GG).left ≫ C.GG.hom = (C.GG ⊗ C.GG).hom := Over.w _
  have w₂ : (snd C.GG C.GG).left ≫ C.GG.hom = (C.GG ⊗ C.GG).hom := Over.w _
  have v₁ : (fst C.A C.A).left ≫ C.A.hom = (C.A ⊗ C.A).hom := Over.w _
  have v₂ : (snd C.A C.A).left ≫ C.A.hom = (C.A ⊗ C.A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst C.GG C.GG).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd C.GG C.GG).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst C.GG C.GG).left = _ ≫ (fst C.GG C.GG).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ C.a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd C.GG C.GG).left = _ ≫ (snd C.GG C.GG).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ C.a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ C.A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst C.A C.A).left = _
      rw [← cancel_mono C.a, IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd C.A C.A).left = _
      rw [← cancel_mono C.a, IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
end GlobalTheory.ZJ.AddExt
