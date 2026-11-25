-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.hom_ext_of_complexPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:33.347889+00:00
-- url     : https://prove2.me/submissions/5165456a-b014-425f-a5af-b30756ae8a1c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_hom_ext_of_points

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
theorem _root_.solution (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (q : Y ⟶ Sp ℂ) [IsSeparated q] {f g : X ⟶ Y} (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g :=
  hom_ext_of_points p q (hf.trans hg.symm) h
end GlobalTheory.ComplexPoints
