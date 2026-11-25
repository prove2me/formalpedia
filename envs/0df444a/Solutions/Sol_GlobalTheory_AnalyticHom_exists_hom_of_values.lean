-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.exists_hom_of_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:55:16.31039+00:00
-- url     : https://prove2.me/submissions/d84f7e95-a90b-438f-8880-4eb5373e0743

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_exists_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] {Z : Type}
  (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
  (hon : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
include hon
namespace GlobalTheory.AnalyticHom
theorem _root_.solution {S : Scheme.{0}} (q : Y ⟶ S) [IsSeparated q] [IsAffine S]
    (h : ∀ z, ∃ (W : X.Opens) (D : Y.Opens), IsAffineOpen D ∧ ⊤ ≤ ex z ⁻¹ᵁ W ∧
      (∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D) ∧
      ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : X ⟶ Y, ∀ z, ex z ≫ g = ey z := by
  first
  | (rename_i h_3 h_4 h_11 h_12; revert X Y p h_3 h_4 Z ex ey hon S q h_11 h_12 h; exact @_root_.GlobalTheory.SchemeHomsFromPoints.exists_hom)
  | exact @_root_.GlobalTheory.SchemeHomsFromPoints.exists_hom
  | exact _root_.GlobalTheory.SchemeHomsFromPoints.exists_hom
  | (apply _root_.GlobalTheory.SchemeHomsFromPoints.exists_hom <;> assumption)
  | (intros; apply _root_.GlobalTheory.SchemeHomsFromPoints.exists_hom <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SchemeHomsFromPoints.exists_hom <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SchemeHomsFromPoints.exists_hom ..)
end GlobalTheory.AnalyticHom
