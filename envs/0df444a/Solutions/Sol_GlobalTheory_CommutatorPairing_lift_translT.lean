-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.lift_translT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:27:44.868776+00:00
-- url     : https://prove2.me/submissions/8b66112d-47ef-48f0-ab67-626e4bc3e664

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution {T Z : Over S} (x : T ⟶ A) (t : Z ⟶ T) (a : Z ⟶ A) :
    lift t a ≫ translT A x = lift t ((t ≫ x) * a) := by
  rw [translT, comp_lift, lift_fst, lift_translPt]
end GlobalTheory.CommutatorPairing
