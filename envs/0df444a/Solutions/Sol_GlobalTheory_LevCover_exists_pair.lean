-- Prove2me | solution 1 for GlobalTheory.LevCover.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:24:33.231798+00:00
-- url     : https://prove2.me/submissions/3d37cb0a-07b0-4149-8679-2cfbdcbcfcdc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsInducedLocus
import Theorems.Thm_GlobalTheory_LevCover_RepTors_ext
import Theorems.Thm_GlobalTheory_LevCover_finiteEtale_tensor
import Theorems.Thm_GlobalTheory_LevelTwist_twist_ev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LevelTwist.twist_ev



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
namespace GlobalTheory.LevCover
theorem _root_.solution {G : Over S} [GrpObj G] {n m : ℕ} {La : Type} [AddCommGroup La] {Z₁ Z₂ : Over S}
    {e₁ : La → (Z₁ ⟶ G)} {e₂ : La → (Z₂ ⟶ G)} (R₁ : RepTors G n La Z₁ e₁) (R₂ : RepTors G m La Z₂ e₂) :
    ∃ (Z : Over S) (χ θ : La → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, χ (a + c) = χ a * χ c) ∧
      (∀ a, χ a ^ n = 1) ∧ (∀ a c, θ (a + c) = θ a * θ c) ∧ (∀ a, θ a ^ m = 1) ∧
      (∀ (T : Over S) (u u' : T ⟶ Z), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u') ∧
      ∀ (T : Over S) (χ' θ' : La → (T ⟶ G)), (∀ a c, χ' (a + c) = χ' a * χ' c) → (∀ a, χ' a ^ n = 1) →
        (∀ a c, θ' (a + c) = θ' a * θ' c) → (∀ a, θ' a ^ m = 1) →
        ∃ h : T ⟶ Z, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a := by
  have := R₁.1
  have := R₁.2.1
  have := R₂.1
  have := R₂.2.1
  obtain ⟨h1, h2⟩ := finiteEtale_tensor Z₁ Z₂
  refine ⟨Z₁ ⊗ Z₂, fun a => fst _ _ ≫ e₁ a, fun a => snd _ _ ≫ e₂ a, h1, h2, fun a c => ?_, fun a => ?_,
    fun a c => ?_, fun a => ?_, fun T u u' hu hu' => ?_, fun T χ' θ' a1 p1 a2 p2 => ?_⟩
  · simp only [R₁.2.2.1, MonObj.comp_mul]
  · beta_reduce; rw [← MonObj.comp_pow, R₁.2.2.2.1, MonObj.comp_one]
  · simp only [R₂.2.2.1, MonObj.comp_mul]
  · beta_reduce; rw [← MonObj.comp_pow, R₂.2.2.2.1, MonObj.comp_one]
  · exact CartesianMonoidalCategory.hom_ext _ _ (R₁.ext fun a => by simpa using hu a)
      (R₂.ext fun a => by simpa using hu' a)
  · obtain ⟨z₁, hz₁, -⟩ := R₁.2.2.2.2 T χ' a1 p1
    obtain ⟨z₂, hz₂, -⟩ := R₂.2.2.2.2 T θ' a2 p2
    exact ⟨lift z₁ z₂, fun a => by simpa using hz₁ a, fun a => by simpa using hz₂ a⟩
end GlobalTheory.LevCover
