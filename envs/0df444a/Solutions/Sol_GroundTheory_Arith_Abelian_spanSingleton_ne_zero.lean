-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.spanSingleton_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:00.048815+00:00
-- url     : https://prove2.me/submissions/ef1b57d8-2874-4f64-b068-d9a4dac8a0e3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd

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
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F] [W.IsElliptic]
omit [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f ≠ 0 :=
  FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hf
end GroundTheory.Arith.Abelian
