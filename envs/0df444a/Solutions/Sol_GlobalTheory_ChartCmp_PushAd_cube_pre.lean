-- Prove2me | solution 1 for GlobalTheory.ChartCmp.PushAd.cube_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:33.79041+00:00
-- url     : https://prove2.me/submissions/a0bc3dd1-c7d4-44ed-b5e5-fa00ef796eb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AdjointnessSeriesTransportFrames

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.PushAd
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
namespace GlobalTheory.ChartCmp.PushAd
theorem _root_.solution (t : SAB H X0) {T T' : Over X0} (h : T' ⟶ T) (a b : T ⟶ t.G) (I : ULift (Finset (Fin 2))) :
    h.left ≫ cφG t ![a, b] I = cφG t ![h ≫ a, h ≫ b] I := by
  rw [show (![h ≫ a, h ≫ b] : Fin 2 → (T' ⟶ t.G)) = fun i => h ≫ ![a, b] i from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  exact congrArg (fun z => z.left) (foldr_padd_pre h ![a, b] _).symm
end GlobalTheory.ChartCmp.PushAd
