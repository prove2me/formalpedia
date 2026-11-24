-- Prove2me | solution 1 for GlobalTheory.existsUnique_hom_of_locally_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:47.712529+00:00
-- url     : https://prove2.me/submissions/32d082b6-cfa2-4c1a-8644-59c9ea640b87

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniqueHomOfLocallyRegular
import Theorems.Thm_GlobalTheory_PointwiseRegular_existsUnique_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y : Over (Sp ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) :=
  fun _ _ _ _ _ _ F h => PointwiseRegular.existsUnique_hom F h
end GlobalTheory
