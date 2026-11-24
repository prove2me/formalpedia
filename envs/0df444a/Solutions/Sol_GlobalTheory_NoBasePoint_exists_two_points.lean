-- Prove2me | solution 1 for GlobalTheory.NoBasePoint.exists_two_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:27:10.323795+00:00
-- url     : https://prove2.me/submissions/dac6fcbb-9156-4578-8c51-a995e111966f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSecValueIsUnit
import Theorems.Thm_GlobalTheory_NoBasePoint_exists_section_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.NoBasePoint
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
namespace GlobalTheory.NoBasePoint
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S)
    [LocallyOfFiniteType A.hom] [IsIntegral (Over.mk t ⊗ A).left] (D : (Over.mk t ⊗ A).left.Opens)
    (hD : (D : Set (Over.mk t ⊗ A).left).Nonempty) (x c : Over.mk t ⟶ A) :
    ∃ a : Over.mk t ⟶ A, (∀ p, (ptSecT A (a * x)).left p ∈ D) ∧ ∀ p, (ptSecT A (a⁻¹ * c)).left p ∈ D := by
  let T := Over.mk t
  let u₁ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A * (fst T A ≫ x))
  let w₁ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A * (fst T A ≫ x)⁻¹)
  let u₂ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((snd T A)⁻¹ * (fst T A ≫ c))
  let w₂ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((fst T A ≫ c) * (snd T A)⁻¹)
  have e₁ : w₁ ≫ u₁ = 𝟙 _ := by
    ext <;> simp [u₁, w₁, MonObj.comp_mul]
  have e₂ : w₂ ≫ u₂ = 𝟙 _ := by
    ext <;> simp [u₂, w₂, MonObj.comp_mul, GrpObj.comp_inv]
  have ne : ∀ u w : T ⊗ A ⟶ T ⊗ A, w ≫ u = 𝟙 _ → ((u.left ⁻¹ᵁ D : (T ⊗ A).left.Opens) : Set (T ⊗ A).left).Nonempty := by
    intro u w e
    obtain ⟨d, hd⟩ := hD
    refine ⟨w.left d, ?_⟩
    show u.left (w.left d) ∈ D
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact hd
  have hne : ((u₁.left ⁻¹ᵁ D ⊓ u₂.left ⁻¹ᵁ D : (T ⊗ A).left.Opens) : Set (T ⊗ A).left).Nonempty :=
    nonempty_preirreducible_inter (u₁.left ⁻¹ᵁ D).isOpen (u₂.left ⁻¹ᵁ D).isOpen (ne _ _ e₁) (ne _ _ e₂)
  have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Spec (CommRingCat.of K)) (fst T A).left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
  obtain ⟨σ, hσ, hm⟩ := exists_section_mem (Y := (T ⊗ A).left) (fst T A).left _ hne
  let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
    rw [← Over.w (fst T A), ← Category.assoc]
    exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
  have hf : σ' ≫ fst T A = 𝟙 T := Over.OverMorphism.ext hσ
  have f₁ : σ' ≫ u₁ = ptSecT A ((σ' ≫ snd T A) * x) := by
    simp [u₁, ptSecT, comp_lift, MonObj.comp_mul, hf, reassoc_of% hf]
  have f₂ : σ' ≫ u₂ = ptSecT A ((σ' ≫ snd T A)⁻¹ * c) := by
    simp [u₂, ptSecT, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, hf, reassoc_of% hf]
  refine ⟨σ' ≫ snd T A, fun p => ?_, fun p => ?_⟩
  · rw [← f₁]; exact (hm p).1
  · rw [← f₂]; exact (hm p).2
end GlobalTheory.NoBasePoint
