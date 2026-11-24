-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.XIdeal_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:39.475637+00:00
-- url     : https://prove2.me/submissions/7e697d85-570b-476b-8156-2284d1a12abe

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_X_sub_C

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
theorem _root_.solution (x : F) : XIdeal W.toAffine x =
    (Ideal.span {X - C x}).map (algebraMap F[X] W.toAffine.CoordinateRing) := by
  rw [XIdeal, Ideal.map_span, Set.image_singleton, algebraMap_X_sub_C]
end GroundTheory.Arith.Abelian
