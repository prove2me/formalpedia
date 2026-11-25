-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.periodForm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:41.049047+00:00
-- url     : https://prove2.me/submissions/4f8940ed-c32f-4d70-bf2f-898a647d973d

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
variable [IsLocalRing R] {Γ : Type} [AddCommGroup Γ] (v : LatticeVal R Γ)
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
theorem _root_.solution (D : DegPre R) (a b : D.X) : periodForm v D a b = periodForm v D b a := by
  simp only [periodForm, add_comm a b]; abel
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
