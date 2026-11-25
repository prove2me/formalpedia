-- Prove2me | solution 1 for GlobalTheory.SS.TorusSlice.isPullback_sweep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:19.047685+00:00
-- url     : https://prove2.me/submissions/2f741f17-289f-479a-aa8d-bb2fe5b000e8

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
variable {S : Scheme.{0}}
namespace GlobalTheory.SS.TorusSlice
theorem _root_.solution {T G Y Y₁ W : Over S} [GrpObj T] [GrpObj G] (i : T ⟶ G) [IsMonHom i] (j : Y ⟶ G) [Mono j]
    (σ : Y ⟶ T) (hσ : Equivar i j σ) (e : Y₁ ⟶ Y) (he : IsPullback e (toUnit Y₁) σ η[T])
    (p : W ⟶ T ⊗ Y) (r : W ⟶ Y) (hW : IsPullback p r (((snd T Y ≫ σ)⁻¹ ≫ i) * (snd T Y ≫ j)) j) :
    ∃ q, IsPullback q p ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) ((fst T Y ≫ i) * (snd T Y ≫ j)) := by
  have he1 : e ≫ σ = 1 := he.w
  have hpr : r ≫ j = ((p ≫ snd T Y ≫ σ)⁻¹ ≫ i) * ((p ≫ snd T Y) ≫ j) := by
    rw [← hW.w]
    simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  have hr : r ≫ σ = 1 := by
    rw [hσ _ _ _ _ hpr, Category.assoc, inv_mul_cancel]
  obtain ⟨r', er, -⟩ := he.exists_lift r (toUnit _) hr
  have key : ∀ {Z : Over S} (u : Z ⟶ T ⊗ Y₁) (v : Z ⟶ T ⊗ Y),
      u ≫ ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) = v ≫ ((fst T Y ≫ i) * (snd T Y ≫ j)) →
      u ≫ fst T Y₁ = (v ≫ fst T Y) * (v ≫ snd T Y ≫ σ) ∧
        v ≫ (((snd T Y ≫ σ)⁻¹ ≫ i) * (snd T Y ≫ j)) = (u ≫ snd T Y₁ ≫ e) ≫ j := by
    intro Z u v h
    have h1 : (v ≫ snd T Y) ≫ j = (((v ≫ fst T Y)⁻¹ * (u ≫ fst T Y₁)) ≫ i) * ((u ≫ snd T Y₁ ≫ e) ≫ j) := by
      simp only [MonObj.comp_mul] at h
      rw [MonObj.mul_comp, GrpObj.inv_comp, _root_.mul_assoc, eq_inv_mul_iff_mul_eq]
      simpa using h.symm
    have h2 := hσ _ _ _ _ h1
    simp only [Category.assoc, he1, MonObj.comp_one, _root_.mul_one] at h2
    refine ⟨by rw [h2, mul_inv_cancel_left], ?_⟩
    simp only [MonObj.comp_mul]
    rw [← Category.assoc v (snd T Y) j, h1, ← h2, ← Category.assoc v, GrpObj.comp_inv, GrpObj.inv_comp,
      inv_mul_cancel_left]
  have hp : Mono p := ⟨fun a b h => hW.hom_ext h (by rw [← cancel_mono j, Category.assoc, Category.assoc, ← hW.w, reassoc_of% h])⟩
  refine ⟨lift ((p ≫ fst T Y) * (p ≫ snd T Y ≫ σ)) r', ⟨?_⟩,
    ⟨PullbackCone.IsLimit.mk _ (fun s => hW.lift s.snd _ (key _ _ s.condition).2) (fun s => ?_)
      (fun s => hW.lift_fst _ _ _) fun s l h1 h2 => ?_⟩⟩
  · simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, reassoc_of% er, hpr, MonObj.mul_comp,
      GrpObj.inv_comp]
    simp [_root_.mul_assoc]
  · ext1
    · simp [MonObj.comp_mul, (key _ _ s.condition).1]
    · refine he.hom_ext ?_ (toUnit_unique _ _)
      simp [er]
  · rw [← cancel_mono p, h2]
    exact (hW.lift_fst _ _ _).symm
end GlobalTheory.SS.TorusSlice
