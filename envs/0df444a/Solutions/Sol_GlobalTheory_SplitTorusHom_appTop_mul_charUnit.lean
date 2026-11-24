-- Prove2me | solution 1 for GlobalTheory.SplitTorusHom.appTop_mul_charUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:14.632397+00:00
-- url     : https://prove2.me/submissions/e1669d4a-1533-4b5e-bcaa-72e723805902

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
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
theorem _root_.solution {Z : Over S} (a b : Z ⟶ splitTorus S X) (χ : X) :
    (a * b).left.appTop.hom (charUnit S X χ).val =
      a.left.appTop.hom (charUnit S X χ).val * b.left.appTop.hom (charUnit S X χ).val := by
  rw [← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val,
    map_mul]
  rfl
end GlobalTheory.SplitTorusHom
