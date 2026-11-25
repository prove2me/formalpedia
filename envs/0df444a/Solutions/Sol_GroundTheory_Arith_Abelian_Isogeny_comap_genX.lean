-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Isogeny.comap_genX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:06.204354+00:00
-- url     : https://prove2.me/submissions/3751e1f1-53f8-4913-8ea4-82b4117eda65

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Theorems.Thm_GroundTheory_Arith_Abelian_liftPoint_genX


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
variable (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
open GroundTheory.Arith.Abelian.Isogeny
variable {E E'} (φ : Isogeny E E')
omit [E.IsElliptic] [E'.IsElliptic]
namespace GroundTheory.Arith.Abelian.Isogeny
theorem _root_.solution : φ.comap (genX E') = φ.x := liftPoint_genX _ _ _
end GroundTheory.Arith.Abelian.Isogeny
