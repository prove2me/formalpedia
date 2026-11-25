-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit.unifAt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:00:32.89858+00:00
-- url     : https://prove2.me/submissions/9218f74e-332a-45d0-a517-d29417254dd2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UniformizationClosedSplit

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
theorem _root_.solution (h₁ : ModelAt Xo c) (h₂ : UnifOfModel Xo c) : UnifAt Xo c :=
  fun la hla T io e ho => h₂ T io (h₁ la hla T io e ho)
end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
