-- Prove2me | solution 1 for GlobalTheory.eq_one_of_fibre_const_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.438625+00:00
-- url     : https://prove2.me/submissions/4f552c76-7e1a-42d9-9a53-df7e9cd5176a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOneOfFibreConstOfSection
import Theorems.Thm_GlobalTheory_FunDescent_comp_appTop_apply
import Theorems.Thm_GlobalTheory_FunDescent_exists_appTop_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (B W : Over S) [GrpObj B], IsAbelianScheme B → ∀ (π : W ⟶ B) [Flat π.left] [Surjective π.left] [QuasiCompact π.left] (ρ : Γ(W.left, ⊤)) (σ : 𝟙_ (Over S) ⟶ W), (∀ (Z : Over S) (g₁ g₂ : Z ⟶ W), g₁ ≫ π = g₂ ≫ π → g₁.left.appTop.hom ρ = g₂.left.appTop.hom ρ) → σ.left.appTop.hom ρ = 1 → ρ = 1 := by
  intro hG S B W _ hB π _ _ _ ρ σ h hσ
  obtain ⟨a, rfl⟩ := FunDescent.exists_appTop_eq π.left ρ (by
    intro Z g₁ g₂ e
    let Z' : Over S := Over.mk (g₂ ≫ W.hom)
    let k₂ : Z' ⟶ W := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ W := Over.homMk g₁ (by
      change g₁ ≫ W.hom = g₂ ≫ W.hom
      rw [← Over.w π, reassoc_of% e])
    exact h Z' k₁ k₂ (Over.OverMorphism.ext e))
  obtain ⟨s, rfl⟩ := (hG S B hB).2 a
  rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, Category.assoc, Over.w π,
    Over.w σ] at hσ
  have hs : s = 1 := by
    have e : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [e] at hσ
    simpa using hσ
  rw [hs, map_one, map_one]
end GlobalTheory
