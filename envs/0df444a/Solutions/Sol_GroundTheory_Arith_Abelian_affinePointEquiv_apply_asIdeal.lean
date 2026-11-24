-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.affinePointEquiv_apply_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:40.539998+00:00
-- url     : https://prove2.me/submissions/b70855d2-ede6-4f23-8334-ebe7f008523f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors

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
variable [IsAlgClosed F]
variable [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (p : {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2}) :
    (affinePointEquiv W p).asIdeal = XYIdeal W.toAffine p.1.1 (C p.1.2) := rfl
end GroundTheory.Arith.Abelian
