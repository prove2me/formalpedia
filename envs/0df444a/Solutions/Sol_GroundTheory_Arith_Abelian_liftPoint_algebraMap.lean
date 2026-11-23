-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.liftPoint_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:09.057813+00:00
-- url     : https://prove2.me/submissions/129f413d-c4e5-459b-8dc7-817982022c31

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable {L : Type*} [Field L] [Algebra F L] {u v : L}
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (h : (W.baseChange L).toAffine.Equation u v)
    (hu : Transcendental F u) (a : W.toAffine.CoordinateRing) :
    liftPoint W h hu (algebraMap _ _ a) = evalAt W h a :=
  IsFractionRing.lift_algebraMap (evalAt_injective W h hu) a
end GroundTheory.Arith.Abelian
