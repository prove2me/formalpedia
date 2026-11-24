-- Prove2me | solution 1 for GlobalTheory.RawChartBC.psTrunc_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:10.175688+00:00
-- url     : https://prove2.me/submissions/18d89797-2424-46d9-95f4-9e0a5fda78df

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
namespace GlobalTheory.RawChartBC
theorem _root_.solution {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (f : MvPowerSeries κ S) :
    psTrunc m (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psTrunc m f) := by
  unfold psTrunc
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]
end GlobalTheory.RawChartBC
