-- Prove2me | solution 1 for GlobalTheory.ChartCmp.PushAd.val_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:59:15.145958+00:00
-- url     : https://prove2.me/submissions/1971d107-76e5-48b2-b19f-2b0027f99163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AdjointnessSeriesTransportFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
theorem _root_.solution (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)
end GlobalTheory.ChartCmp.PushAd
