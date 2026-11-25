-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordLaw.cc_comp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:03.472009+00:00
-- url     : https://prove2.me/submissions/41b0104f-42a3-4e48-9870-ec035cb0efce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_cc_ev

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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V] {d : ℕ}
namespace GlobalTheory.ChartCmp.CoordLaw
theorem _root_.solution {n : ℕ} {φ : Pt V 1 d} {a : Pt V n d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin d) : MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  cc_ev _ (fun j i => by rw [Matrix.cons_val_fin_one]; exact ha i) _ (hφ i)
end GlobalTheory.ChartCmp.CoordLaw
