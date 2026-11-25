-- Prove2me | solution 1 for GlobalTheory.EffCartierData.lb_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:40.209115+00:00
-- url     : https://prove2.me/submissions/c86a24ff-8ead-4e27-9b31-cbf2117c05bd

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution (a : Γ(X, ⊤)) (ha : IsRegularFn a) : (principal a ha).lb = LB.triv X := by
  have : (principal a ha).trans = fun _ _ => 1 := funext fun i => funext fun j =>
    ((principal a ha).eq_trans i j (u := 1) (one_mul _).symm).symm
  exact congrArg (LB.mk PUnit fun _ => ⊤) this
end GlobalTheory.EffCartierData
