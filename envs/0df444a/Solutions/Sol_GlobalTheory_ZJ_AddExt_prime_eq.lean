-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:01.870927+00:00
-- url     : https://prove2.me/submissions/43600379-70b9-4183-97df-fe71c4530e62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_GlobalTheory_ZJ_AddExt_natCast_eq_zero_of_closedPoint

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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution (p q : ℕ) [Fact p.Prime] [Fact q.Prime] {K : Type} [Field K] (u : Sp K ⟶ Sp (OO p))
    (u' : Sp K ⟶ Sp (OO q)) (hu : ∀ x, u x = cPt p) (hu' : ∀ x, u' x = cPt q) : p = q := by
  have h1 := natCast_eq_zero_of_closedPoint p u hu
  have h2 := natCast_eq_zero_of_closedPoint q u' hu'
  have := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h1
  have := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).2 h2
  exact CharP.eq K ‹CharP K p› ‹CharP K q›
end GlobalTheory.ZJ.AddExt
