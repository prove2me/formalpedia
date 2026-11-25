-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.fieldRange_ratEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:02.581218+00:00
-- url     : https://prove2.me/submissions/41d8b1c1-973c-4a1c-8fd3-fedf6911fc08

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Theorems.Thm_GroundTheory_Arith_Abelian_ratEmb_X
import Theorems.Thm_GroundTheory_Arith_Abelian_map_top_eq_fieldRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
universe u
variable {F : Type u} [Field F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
omit [E.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : (ratEmb E).fieldRange = F⟮genX E⟯ := by
  rw [← map_top_eq_fieldRange, ← RatFunc.adjoin_X, adjoin_map, Set.image_singleton, ratEmb_X]
end GroundTheory.Arith.Abelian
