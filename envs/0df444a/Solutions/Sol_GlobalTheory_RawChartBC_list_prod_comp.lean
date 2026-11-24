-- Prove2me | solution 1 for GlobalTheory.RawChartBC.list_prod_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:14:59.611563+00:00
-- url     : https://prove2.me/submissions/401fa151-6d1b-4ee9-91b0-2a5fc57dd401

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawChartBC
open ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)
namespace GlobalTheory.RawChartBC
theorem _root_.solution {T T' : Over Xo.X} (f : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]
end GlobalTheory.RawChartBC
