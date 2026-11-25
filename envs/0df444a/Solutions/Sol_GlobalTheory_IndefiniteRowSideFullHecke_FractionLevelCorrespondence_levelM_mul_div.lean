-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence.levelM_mul_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:51.454514+00:00
-- url     : https://prove2.me/submissions/b33d9dff-8682-4247-8da8-557a1cd5acab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FractionLevelCorrespondence

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
theorem _root_.solution (x : ArcInput D c β O' b) (y z : x.P.X) :
    (l.M : ℤ) * (x.be y z / (l.M : ℤ)) = x.be y z :=
  Int.mul_ediv_cancel' (((Int.natCast_dvd_natCast.2 (Nat.dvd_lcm_left l.M l.A)).mul_left 2).trans
    (x.be_dvd y z))
end GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
