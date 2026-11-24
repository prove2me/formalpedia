-- Prove2me | solution 1 for GlobalTheory.SplitTorusHom.exists_addMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:16:29.314106+00:00
-- url     : https://prove2.me/submissions/51342b2f-3629-4ab5-a8aa-b32c32101f2f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
import Theorems.Thm_GlobalTheory_SplitTorusHom_charUnit_add
import Theorems.Thm_GlobalTheory_SplitTorusHom_existsUnique_pullback_charUnit
import Theorems.Thm_GlobalTheory_SplitTorusHom_charUnit_injective

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
theorem _root_.solution [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] :
    ∃ φ : X →+ X', ∀ χ, f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by
  choose c hc using fun χ => (existsUnique_pullback_charUnit f χ).exists
  refine ⟨AddMonoidHom.mk' c fun a b => charUnit_injective (S := S) ?_, hc⟩
  rw [← hc, charUnit_add, charUnit_add, map_mul, hc, hc]
end GlobalTheory.SplitTorusHom
