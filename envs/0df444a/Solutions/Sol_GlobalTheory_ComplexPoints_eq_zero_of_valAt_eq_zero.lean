-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.eq_zero_of_valAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:07.663257+00:00
-- url     : https://prove2.me/submissions/cd55caea-5ac8-4cfa-b3d2-ae1afdff7d45

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
theorem _root_.solution (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
    (f : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f = 0) : f = 0 := by
  refine eq_zero_of_basicOpen_eq_bot f (le_bot_iff.1 (opens_le_of_geomPoints p (𝟙 _) _ _ ?_))
  intro x hx hxf
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := fun a ha => X.basicOpen_le f (hxf ha)
  exact absurd (h x hxU hx) ((top_le_preimage_basicOpen_iff x U hxU f).1 hxf)
end GlobalTheory.ComplexPoints
