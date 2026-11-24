-- Prove2me | solution 1 for GlobalTheory.SplitTorusHom.charUnit_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:54.492799+00:00
-- url     : https://prove2.me/submissions/556f446c-71be-4f91-ae1f-47bb1d63a4f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
import Theorems.Thm_GlobalTheory_SplitTorusHom_appTop_id
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.SplitTorusHom
variable {S : Scheme.{0}}
variable {X X' : Type} [AddCommGroup X] [AddCommGroup X']
namespace GlobalTheory.SplitTorusHom
theorem _root_.solution (x y : X) :
    (charUnit S X (x + y)).val = (charUnit S X x).val * (charUnit S X y).val := by
  have h (z : X) := (splitTorusPointsEquiv_val S X _ (𝟙 _) z).trans (appTop_id _)
  rw [← h, ← h, ← h, ofAdd_add, map_mul, Units.val_mul]
end GlobalTheory.SplitTorusHom
