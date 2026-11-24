-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordAtIdeal_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:35:59.333992+00:00
-- url     : https://prove2.me/submissions/23009470-08ac-463b-8644-e9c2727fa6d9

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
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    (a : W.toAffine.CoordinateRing) :
    ordAtIdeal W v (algebraMap _ W.toAffine.FunctionField a) =
      FractionalIdeal.count W.toAffine.FunctionField v
        ((Ideal.span {a} : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  rw [ordAtIdeal, FractionalIdeal.coeIdeal_span_singleton]
end GroundTheory.Arith.Abelian
