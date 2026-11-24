-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.isUnit_of_valAt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:56:02.543184+00:00
-- url     : https://prove2.me/submissions/ddc13d61-7c95-438f-a13e-65abac223eb1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_opens_le_of_geomPoints
import Theorems.Thm_GlobalTheory_ComplexPoints_top_le_preimage_basicOpen_iff

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
theorem _root_.solution (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f ≠ 0) : IsUnit f := by
  have hU : U ≤ X.basicOpen f := opens_le_of_geomPoints p (𝟙 _) U _ fun x hx hxU =>
    (top_le_preimage_basicOpen_iff x U hxU f).2 (h x hxU hx)
  exact X.toRingedSpace.isUnit_of_isUnit_germ U f fun y hy => (X.mem_basicOpen f y hy).1 (hU hy)
end GlobalTheory.ComplexPoints
