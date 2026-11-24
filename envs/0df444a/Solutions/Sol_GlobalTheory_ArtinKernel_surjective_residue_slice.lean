-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.surjective_residue_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:12.604802+00:00
-- url     : https://prove2.me/submissions/ddba6501-dbad-44b3-8283-ccc153ed00d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
import Theorems.Thm_GlobalTheory_ArtinKernel_resPt_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {A : Over (Sp ℂ)}
namespace GlobalTheory.ArtinKernel
theorem _root_.solution [Subsingleton (PrimeSpectrum R)] (ρ : R →ₐ[ℂ] ℂ) :
    Function.Surjective (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left := by
  have hc : spMap ρ.toRingHom ≫ spMap (algebraMap ℂ R) = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact ρ.commutes a
  have wP : (fst (spO R) A).left ≫ (spO R).hom = (snd (spO R) A).left ≫ A.hom :=
    (Over.w (fst (spO R) A)).trans (Over.w (snd (spO R) A)).symm
  have hL1 : (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left ≫ (fst (spO R) A).left = A.hom ≫ spMap ρ.toRingHom := by
    rw [← Over.comp_left, lift_fst, Over.comp_left, resPt_left]
    rfl
  have hL2 : (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left ≫ (snd (spO R) A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  intro p
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap ρ.toRingHom)
    (g := (fst (spO R) A).left) q p (Subsingleton.elim (α := PrimeSpectrum R) _ _)
  have cond : pullback.fst (spMap ρ.toRingHom) (fst (spO R) A).left ≫ spMap ρ.toRingHom =
      pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (fst (spO R) A).left := pullback.condition
  have hq1 : pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left ≫ A.hom =
      pullback.fst (spMap ρ.toRingHom) (fst (spO R) A).left := by
    rw [← wP, ← Category.assoc, ← cond, Category.assoc, show (spO R).hom = spMap (algebraMap ℂ R) from rfl, hc,
      Category.comp_id]
  have key : (pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left) ≫
      (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left = pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left := by
    apply Over.tensorObj_ext
    · show ((pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left) ≫
          (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left) ≫ (fst (spO R) A).left =
          pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (fst (spO R) A).left
      rw [Category.assoc, hL1, ← cond, ← hq1]
      simp only [Category.assoc]
    · show ((pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left) ≫
          (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left) ≫ (snd (spO R) A).left =
          pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left
      rw [Category.assoc, hL2, Category.comp_id]
  refine ⟨(pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, key, hw2]
end GlobalTheory.ArtinKernel
