-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.opens_eq_top_of_complexPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:38.121916+00:00
-- url     : https://prove2.me/submissions/2c7b31fa-ca6c-41a2-bac8-9134f2d719fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_opens_le_of_complexPoints

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
theorem _root_.solution (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U) : U = ⊤ :=
  top_le_iff.1 (opens_le_of_complexPoints p ⊤ U fun x hx _ => h x hx)
end GlobalTheory.ComplexPoints
