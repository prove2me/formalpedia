-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.psiAt_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:29.890872+00:00
-- url     : https://prove2.me/submissions/a904f285-396a-4598-a3ca-c829c344cf72

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_eq

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
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (x y : R) (n : ℤ) : psiAt W x y (-n) = -psiAt W x y n := by
  simp [psiAt_eq, normEDS_neg]
end GroundTheory.Arith.Abelian
