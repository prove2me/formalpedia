-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.finite_support_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:24.438429+00:00
-- url     : https://prove2.me/submissions/d64ada8a-e373-4be7-9ebe-91fb15b43883

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
variable [IsAlgClosed F] [W.IsElliptic]
omit [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution [IsDedekindDomain W.toAffine.CoordinateRing]
    (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) :
    (Function.support fun v : HeightOneSpectrum W.toAffine.CoordinateRing =>
      FractionalIdeal.count W.toAffine.FunctionField v I).Finite :=
  Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
end GroundTheory.Arith.Abelian
