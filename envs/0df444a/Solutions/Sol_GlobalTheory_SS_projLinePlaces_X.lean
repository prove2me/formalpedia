-- Prove2me | solution 1 for GlobalTheory.SS.projLinePlaces_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:07:54.517998+00:00
-- url     : https://prove2.me/submissions/3a32cabd-3110-41b9-93fe-87ce62cd491e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SS
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
open Polynomial IsDedekindDomain
variable (k : Type) [Field k]
variable {k}
variable (k)
namespace GlobalTheory.SS
theorem _root_.solution : (projLinePlaces k).v none (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = -1 := by
  show plOrd k none RatFunc.X = -1
  rw [← RatFunc.algebraMap_X, plOrd_none Polynomial.X_ne_zero, Polynomial.natDegree_X]
  rfl
end GlobalTheory.SS
