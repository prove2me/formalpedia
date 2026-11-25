-- Prove2me | solution 1 for GlobalTheory.GrpDescent.isPullback_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:07:41.73048+00:00
-- url     : https://prove2.me/submissions/edfcc271-1149-4029-b702-cc23c62c911b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsDescendToLargeSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToLargeSubfield
import Theorems.Thm_GlobalTheory_GrpDescent_isSquare_sq
import Theorems.Thm_GlobalTheory_GrpDescent_sq_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
open GlobalTheory GlobalTheory.GrpDescent
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
namespace GlobalTheory.GrpDescent
theorem _root_.solution (hA : IsPullback φ A.hom G.hom j) :
    IsPullback (sq hA.w) (A ⊗ A).hom (G ⊗ G).hom j := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := (isSquare_sq hA.w).1
  have h₂ := (isSquare_sq hA.w).2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply sq_ext
    · rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]
end GlobalTheory.GrpDescent
