-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordLaw.eq_comp1_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:49.778233+00:00
-- url     : https://prove2.me/submissions/a5deafba-eab9-4742-b722-0bdb33edf005

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_germCompOne_assoc_of_constantCoeff_zero
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_germCompOne_identityPoint_left

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
theorem _root_.solution {n : ℕ} {φ φi : Pt V 1 d} (h : IsInvPair φ φi) {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (e : comp1 φ a = b) : a = comp1 φi b := by
  rw [← e, ← germCompOne_assoc_of_constantCoeff_zero φi φ a h.1 ha, h.2.2.2, germCompOne_identityPoint_left a ha]
end GlobalTheory.ChartCmp.CoordLaw
