-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing.constUnit_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:49.970919+00:00
-- url     : https://prove2.me/submissions/3749d78b-f1d4-4beb-b2ec-259d636633ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_ConstantUnitPairing

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
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] : Function.Bijective (constUnit R F) :=
  (Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective
end GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
