-- Prove2me | solution 1 for GlobalTheory.ToSplit.exists_unit_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:44:02.898101+00:00
-- url     : https://prove2.me/submissions/0c2e54b6-08ab-4ae9-ba21-97da199a8a22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_GlobalTheory_FunDescent_exists_app_eq
import Theorems.Thm_GlobalTheory_FunDescent_isUnit_of_isUnit_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X Y : Over S} (π : Y ⟶ X) [Flat π.left] [Surjective π.left]
  [QuasiCompact π.left]
namespace GlobalTheory.ToSplit
theorem _root_.solution (U : X.left.Opens) (f : Γ(Y.left, π.left ⁻¹ᵁ U)ˣ)
    (hf : ∀ (Z : Over S) (g₁ g₂ : Z ⟶ Y) (z : Z.left), g₁ ≫ π = g₂ ≫ π → π.left (g₁.left z) ∈ U →
      π.left (g₂.left z) ∈ U → gm g₁.left z _ f = gm g₂.left z _ f) :
    ∃ a : Γ(X.left, U)ˣ, pullU π.left U a = f := by
  obtain ⟨a, ha⟩ := FunDescent.exists_app_eq π.left U f.val fun Z g₁ g₂ h₁ h₂ e => by
    let Z' : Over S := Over.mk (g₂ ≫ Y.hom)
    let k₂ : Z' ⟶ Y := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ Y := Over.homMk g₁ (by
      change g₁ ≫ Y.hom = g₂ ≫ Y.hom
      rw [← Over.w π, reassoc_of% e])
    have : res h₁ (pullU g₁ _ f) = res h₂ (pullU g₂ _ f) := unit_ext fun z hz => by
      rw [gm_id_res_pull g₁ z h₁ hz, gm_id_res_pull g₂ z h₂ hz]
      exact hf Z' k₁ k₂ z (Over.OverMorphism.ext e) (h₁ hz) (h₂ hz)
    exact congrArg Units.val this
  have hu : IsUnit a := FunDescent.isUnit_of_isUnit_app π.left U a (ha ▸ f.isUnit)
  exact ⟨hu.unit, Units.ext ha⟩
end GlobalTheory.ToSplit
