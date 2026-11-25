-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.eq_of_valAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:27.710804+00:00
-- url     : https://prove2.me/submissions/c03fe360-10e3-44f2-ae5d-c472dce38479

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
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
open GlobalTheory GlobalTheory.ComplexPoints
variable {X Y : Scheme.{0}}
namespace GlobalTheory.ComplexPoints
theorem _root_.solution (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
    (f g : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f = valAt x U hx g) :
    f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_valAt_eq_zero p U _ fun x hx hp => ?_
  have := h x hx hp
  unfold valAt at this ⊢
  rw [map_sub, map_sub, this, sub_self]
end GlobalTheory.ComplexPoints
