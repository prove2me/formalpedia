-- Prove2me | solution 1 for GlobalTheory.ChartCmp.PushAd.cube_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:08:29.470201+00:00
-- url     : https://prove2.me/submissions/db8308ef-30dc-4357-97c4-47e94824aeaf

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
theorem _root_.solution (t t' : SAB H X0) (f : t.G ⟶ t'.G) [IsMonHom f] {T : Over X0} (a b : T ⟶ t.G)
    (I : ULift (Finset (Fin 2))) : cφG t ![a, b] I ≫ f.left = cφG t' ![a ≫ f, b ≫ f] I := by
  rw [show (![a ≫ f, b ≫ f] : Fin 2 → (T ⟶ t'.G)) = fun i => ![a, b] i ≫ f from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  exact congrArg (fun z => z.left) (foldr_padd_comp f ![a, b] _)
end GlobalTheory.ChartCmp.PushAd
