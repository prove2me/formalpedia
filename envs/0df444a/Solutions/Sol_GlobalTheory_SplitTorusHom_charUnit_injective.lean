-- Prove2me | solution 1 for GlobalTheory.SplitTorusHom.charUnit_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:46.706799+00:00
-- url     : https://prove2.me/submissions/279f8475-ce38-43c5-8efb-56db64fd19fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
import Theorems.Thm_GlobalTheory_SplitTorusHom_appTop_id
import Theorems.Thm_GlobalTheory_SplitTorusHom_existsUnique_pullback_charUnit
import Theorems.Thm_GlobalTheory_TorusUnit_IsCharNear_unique


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
theorem _root_.solution [ConnectedSpace S] {x y : X}
    (h : (charUnit S X x).val = (charUnit S X y).val) : x = y :=
  (existsUnique_pullback_charUnit (𝟙 (splitTorus S X)) x).unique (appTop_id _)
    ((appTop_id _).trans h)
end GlobalTheory.SplitTorusHom
