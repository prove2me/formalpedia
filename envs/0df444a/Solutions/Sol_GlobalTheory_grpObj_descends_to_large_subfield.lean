-- Prove2me | solution 1 for GlobalTheory.grpObj_descends_to_large_subfield
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:46:01.140956+00:00
-- url     : https://prove2.me/submissions/788b9160-52ce-496d-912d-967e46064d7e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsDescendToLargeSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToLargeSubfield
import Theorems.Thm_GlobalTheory_GrpDescent_isSquare_sq
import Theorems.Thm_GlobalTheory_GrpDescent_eq_sq
import Theorems.Thm_GlobalTheory_GrpDescent_isPullback_sq
import Theorems.Thm_GlobalTheory_GrpDescent_exists_grpObj
import Theorems.Thm_GlobalTheory_GrpDescent_flat_spMap
import Theorems.Thm_GlobalTheory_GrpDescent_surjective_spMap
import Theorems.Thm_GlobalTheory_GrpDescent_spMap_subtype
import Theorems.Thm_GlobalTheory_T_exists_descent_of_morphisms_to_subfield
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GrpDescent
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ := by
  intro K _ K₀ A₀ A _ φ _ _ _ hφ
  have hw := hφ.w
  have hq : QuasiCompact (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiCompact (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  have hs : QuasiSeparated (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiSeparated (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨s₁, H₁⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ (A₀ ⊗ A₀).hom (A ⊗ A).hom (sq hw) _ A₀.hom Unit
    (fun _ => (μ[A]).left ≫ φ) (isPullback_sq hφ) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w, (isPullback_sq hφ).w])
  obtain ⟨s₂, H₂⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ A₀.hom A.hom φ _ A₀.hom Unit
    (fun _ => (ι[A]).left ≫ φ) hφ (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w])
  obtain ⟨s₃, H₃⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ (𝟙 _) (𝟙 _) (spMap K₀.subtype) _ A₀.hom Unit
    (fun _ => (η[A]).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  classical
  refine ⟨s₁ ∪ s₂ ∪ s₃, fun K₁ h hs A₁ φ₁ ψ hφ₁ hψ hψw => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  have hψp : IsPullback ψ A.hom A₁.hom (spMap K₁.subtype) :=
    IsPullback.of_right (by rwa [hψ, spMap_subtype]) hψw hφ₁
  obtain ⟨m, hm⟩ := H₁ K₁ h hs.1.1 _ (A₁ ⊗ A₁).hom (sq hφ₁.w) (sq hψw) (isPullback_sq hφ₁)
    (eq_sq hw ⟨by rw [Category.assoc, (isSquare_sq _).1, reassoc_of% (isSquare_sq hψw).1, hψ],
      by rw [Category.assoc, (isSquare_sq _).2, reassoc_of% (isSquare_sq hψw).2, hψ]⟩) (isPullback_sq hψp).w
  obtain ⟨i, hi⟩ := H₂ K₁ h hs.1.2 _ A₁.hom φ₁ ψ hφ₁ hψ hψw
  obtain ⟨e, he⟩ := H₃ K₁ h hs.2 _ (𝟙 _) (spMap (Subfield.inclusion h)) (spMap K₁.subtype)
    (IsPullback.of_vert_isIso ⟨by simp⟩) (spMap_subtype h) (by simp)
  have := flat_spMap K₁.subtype
  have := surjective_spMap K₁.subtype
  refine exists_grpObj _ hψp
    (Over.homMk (hφ₁.lift (m ()) (A₁ ⊗ A₁).hom ((hm ()).2.trans (isPullback_sq hφ₁).w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (i ()) A₁.hom ((hi ()).2.trans hφ₁.w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (e ()) (𝟙 _) ((he ()).2.trans (by simp))) (hφ₁.lift_snd _ _ _)) ?_ ?_ ?_
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hm ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [(isPullback_sq hψp).w, ← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hi ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (he ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]; simp
end GlobalTheory
