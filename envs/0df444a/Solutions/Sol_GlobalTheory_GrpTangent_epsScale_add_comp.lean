-- Prove2me | solution 1 for GlobalTheory.GrpTangent.epsScale_add_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:35:07.501798+00:00
-- url     : https://prove2.me/submissions/d4bc3f4e-c47f-413a-86d3-ee60c61e126e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_TangentCrit_hom_ext_of_ker_inf
import Theorems.Thm_GlobalTheory_GrpTangent_epsScale_zero_comp
import Theorems.Thm_GlobalTheory_GrpTangent_sqZeroMap_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]
namespace GlobalTheory.GrpTangent
theorem _root_.solution (a b : R) {w : epsR R ⟶ G} (hw : IsTangent w) :
    epsScale (a + b) ≫ w = (epsScale a ≫ w) * (epsScale b ≫ w) := by
  let i₁ := LinearMap.inl R R R
  let i₂ := LinearMap.inr R R R
  have key : sqZeroMap (i₁ + i₂) ≫ w = (sqZeroMap i₁ ≫ w) * (sqZeroMap i₂ ≫ w) := by
    ext1
    refine hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMap (LinearMap.fst R R R) ≫ _ = sqZeroMap (LinearMap.fst R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMap_comp_eq]
      simp [i₁, i₂, epsScale_zero_comp hw]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMap (LinearMap.snd R R R) ≫ _ = sqZeroMap (LinearMap.snd R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMap_comp_eq]
      simp [i₁, i₂, epsScale_zero_comp hw]
  have := congrArg (sqZeroMap (a • LinearMap.fst R R R + b • LinearMap.snd R R R) ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMap_comp_eq] at this
  simpa [i₁, i₂] using this
end GlobalTheory.GrpTangent
