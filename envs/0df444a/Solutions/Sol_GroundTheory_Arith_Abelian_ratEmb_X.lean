-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ratEmb_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:29.682962+00:00
-- url     : https://prove2.me/submissions/2b91166a-0a35-40c9-a848-4b5a7d402004

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny

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
theorem _root_.solution : ratEmb E RatFunc.X = genX E := by
  have := ratEmb_div E X 1
  rw [map_one, div_one, map_one, div_one, aeval_X, RatFunc.algebraMap_X] at this
  exact this
end GroundTheory.Arith.Abelian
