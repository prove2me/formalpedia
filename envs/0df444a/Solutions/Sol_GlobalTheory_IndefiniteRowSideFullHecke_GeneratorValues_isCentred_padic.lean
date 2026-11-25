-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.isCentred_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:59:10.418791+00:00
-- url     : https://prove2.me/submissions/2cad09d8-19f5-44bf-a37b-b554fd63fbb2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    IsCentred (R := ℤ_[p]) (FractionRing.algEquiv ℤ_[p] ℚ_[p]).toRingEquiv.toRingHom where
  le_one r := by
    change ‖FractionRing.algEquiv ℤ_[p] ℚ_[p] (algebraMap _ _ r)‖ ≤ 1
    rw [AlgEquiv.commutes]; exact r.2
  lt_one r hr := by
    change ‖FractionRing.algEquiv ℤ_[p] ℚ_[p] (algebraMap _ _ r)‖ < 1
    rw [AlgEquiv.commutes]; exact PadicInt.mem_nonunits.1 hr
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
