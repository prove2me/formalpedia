-- Prove2me | solution 1 for GlobalTheory.ChartCmp.JetDim.tanAll_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:38.099686+00:00
-- url     : https://prove2.me/submissions/92b01949-15df-4182-b5d1-dffe67b01f7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique

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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JetDim
variable {V : Type} [CommRing V]
namespace GlobalTheory.ChartCmp.JetDim
theorem _root_.solution (κ : Type) [DecidableEq κ] (i : κ) :
    tanAll (V := V) κ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = TrivSqZeroExt.inr (Pi.single i (1 : V)) := by
  show MvPolynomial.aeval _ (MvPolynomial.X i) = _
  simp
end GlobalTheory.ChartCmp.JetDim
