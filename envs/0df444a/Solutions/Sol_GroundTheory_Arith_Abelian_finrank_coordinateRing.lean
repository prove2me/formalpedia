-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.finrank_coordinateRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:38.5518+00:00
-- url     : https://prove2.me/submissions/60f0c73a-2002-4432-9220-1ee0c7ef0ff6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : Module.finrank F[X] W.toAffine.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (CoordinateRing.basis W.toAffine)).trans (Fintype.card_fin 2)
end GroundTheory.Arith.Abelian
