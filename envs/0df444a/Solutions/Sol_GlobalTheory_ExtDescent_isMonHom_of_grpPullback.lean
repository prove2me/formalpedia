-- Prove2me | solution 1 for GlobalTheory.ExtDescent.isMonHom_of_grpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:10:46.090086+00:00
-- url     : https://prove2.me/submissions/aff2aad8-c6ac-4c3c-9bff-3b3723349ff2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescends
import Theorems.Thm_GlobalTheory_ExtDescent_hom_ext_of_points
import Theorems.Thm_GlobalTheory_GrpDense_hom_ext_of_points
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.ExtDescent
variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}
namespace GlobalTheory.ExtDescent
theorem _root_.solution [Flat f] [Surjective f] {X Y : Over S} {X₀ Y₀ : Over S₀}
    [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀] {φ : X.left ⟶ X₀.left} {ψ : Y.left ⟶ Y₀.left}
    (hX : IsGrpPullback X X₀ f φ) (hY : IsGrpPullback Y Y₀ f ψ) (g : X ⟶ Y) (g₀ : X₀ ⟶ Y₀)
    (w : φ ≫ g₀.left = g.left ≫ ψ) [IsMonHom g] : IsMonHom g₀ := by
  have pa : ∀ {T : Over S} (x : T ⟶ X), pushHom hX T x ≫ g₀ = pushHom hY T (x ≫ g) := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, w, Category.assoc])
  have hm : μ[X₀] ≫ g₀ = (g₀ ⊗ₘ g₀) ≫ μ := by
    refine hom_ext_of_points (f := f) fun T t => ?_
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushHom hX T x) (pushHom hX T y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst]; exact hx.symm)
        (by rw [lift_snd]; exact hy.symm)
    rw [← Category.assoc, ← Hom.mul_def, ← map_mul, pa, lift_map_assoc, ← Hom.mul_def, pa, pa,
      ← map_mul, MonObj.mul_comp]
  refine ⟨?_, hm⟩
  have e : (η[X₀] ≫ g₀) * (η[X₀] ≫ g₀) = η[X₀] ≫ g₀ := by
    rw [Hom.mul_def, ← lift_map, Category.assoc, ← hm, ← Category.assoc]
    congr 1
    simpa [Hom.mul_def, Hom.one_def] using _root_.mul_one (1 : 𝟙_ (Over S₀) ⟶ X₀)
  have e' : η[X₀] ≫ g₀ = 1 := by simpa using e
  rw [e', Hom.one_def]; simp
end GlobalTheory.ExtDescent
