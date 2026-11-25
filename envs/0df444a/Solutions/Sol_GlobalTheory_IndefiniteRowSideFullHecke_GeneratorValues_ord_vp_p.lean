-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vp_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:04.018613+00:00
-- url     : https://prove2.me/submissions/a1abc7f5-65a0-4bc9-ad2a-2221ec0ed783

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_ramIdx_pos

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
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]
variable [IsDiscreteValuationRing R]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
theorem _root_.solution {p : ℕ} (hp : IsOverPrime R p) :
    (ord_vp hp).toFun (toUnitK (p : R) hp.ne_zero) = 1 :=
  div_self (Int.cast_ne_zero.2 (ramIdx_pos hp).ne')
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
