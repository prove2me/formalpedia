-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.mulIsogeny_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:55.145506+00:00
-- url     : https://prove2.me/submissions/697fa211-cc41-4b06-88c6-5387760e56c5

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
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℤ} (hn : n ≠ 0) :
    (mulIsogeny E n hn).x = aeval (genX E) (E.Φ n) / aeval (genX E) (E.ΨSq n) :=
  xOf_zsmul_genericPoint E hn
end GroundTheory.Arith.Abelian
