-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.xK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:45.869853+00:00
-- url     : https://prove2.me/submissions/3db0bc99-5db9-4e32-9043-29cbc96d10e4

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
theorem _root_.solution (D : DegPre R) (χ : D.X) : D.xK χ = jK R ≫ (D.c χ).left := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
