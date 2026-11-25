-- Prove2me | solution 1 for GlobalTheory.SemiAbelianTripleChecks.act_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:34.977259+00:00
-- url     : https://prove2.me/submissions/81b1106b-70c8-42c9-9972-d9c0a9bf8269

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_CubeMapTripleProductUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SemiAbelianTripleChecks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
namespace GlobalTheory.SemiAbelianTripleChecks
theorem _root_.solution (t : SAB H S) (a b : 𝓞 E) :
    t.act.act (a + b) = lift (t.act.act a) (t.act.act b) ≫ μ[t.G] := t.act.add a b
end GlobalTheory.SemiAbelianTripleChecks
