-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Isogeny.comap_genY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:16.940985+00:00
-- url     : https://prove2.me/submissions/5a65b3a1-3d61-4a0c-8c0b-99b081197c40

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Theorems.Thm_GroundTheory_Arith_Abelian_liftPoint_genY


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
theorem _root_.solution : φ.comap (genY E') = φ.y := liftPoint_genY _ _ _
end GroundTheory.Arith.Abelian.Isogeny
