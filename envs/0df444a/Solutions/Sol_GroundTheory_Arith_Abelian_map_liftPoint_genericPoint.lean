-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.map_liftPoint_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:27.958077+00:00
-- url     : https://prove2.me/submissions/4f08fd80-fe2e-4665-b45d-5054abf3dc94

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_liftPoint_genX
import Theorems.Thm_GroundTheory_Arith_Abelian_liftPoint_genY
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {L : Type*} [Field L] [Algebra F L] [DecidableEq L] {u v : L}
    (h : (W.baseChange L).toAffine.Nonsingular u v) (hu : Transcendental F u) :
    Point.map (liftPoint W h.1 hu) (genericPoint W) = .some u v h := by
  simp only [genericPoint, Point.map]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Point.some.injEq]
  exact ⟨liftPoint_genX W h.1 hu, liftPoint_genY W h.1 hu⟩
end GroundTheory.Arith.Abelian
