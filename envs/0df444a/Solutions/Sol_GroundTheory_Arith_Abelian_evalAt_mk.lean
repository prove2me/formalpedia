-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.evalAt_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:52.505446+00:00
-- url     : https://prove2.me/submissions/180c62a3-ff8b-499a-874a-160ba7cdf248

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
theorem _root_.solution (h : (W.baseChange L).toAffine.Equation u v) (p : F[X][Y]) :
    evalAt W h (CoordinateRing.mk W p) = p.eval₂ (eval₂RingHom (algebraMap F L) u) v := by
  change AdjoinRoot.lift (eval₂RingHom (algebraMap F L) u) v (eval₂_polynomial W h)
    (AdjoinRoot.mk _ p) = _
  rw [AdjoinRoot.lift_mk]
end GroundTheory.Arith.Abelian
