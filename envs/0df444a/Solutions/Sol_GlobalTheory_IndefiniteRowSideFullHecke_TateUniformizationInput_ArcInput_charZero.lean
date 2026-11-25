-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.ArcInput.charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:59.876372+00:00
-- url     : https://prove2.me/submissions/90b53a9d-6f1b-4743-a45e-0987eee04293

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
attribute [instance] ArcInput.mod
open GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.ArcInput
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
namespace GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.ArcInput
theorem _root_.solution (x : ArcInput D c β O' b) : CharZero (FractionRing O') :=
  x.gam.charZero_iff x.gam.injective |>.mp inferInstance
end GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.ArcInput
