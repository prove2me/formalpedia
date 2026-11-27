-- Prove2me | solution 1 for GlobalTheory.eq_zero_and_isUnit_of_valAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:38:10.181599+00:00
-- url     : https://prove2.me/submissions/5583fcc0-9e17-4498-aba6-ed70f04e0671

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_isUnit_of_valAt_ne_zero
import Theorems.Thm_GlobalTheory_ComplexPoints_eq_zero_of_valAt_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
      (f : Γ(X, U)),
      ((∀ (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U h f = 0) → f = 0) ∧
      ((∀ (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U h f ≠ 0) → IsUnit f) :=
  fun _ p _ _ U f =>
    ⟨ComplexPoints.eq_zero_of_valAt_eq_zero p U f, ComplexPoints.isUnit_of_valAt_ne_zero p U f⟩
end GlobalTheory
