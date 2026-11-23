-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.psiAt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:30.19016+00:00
-- url     : https://prove2.me/submissions/6ed80989-f7f9-4c1b-9370-77bb293886c7

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
theorem _root_.solution (x y : R) : psiAt W x y 1 = 1 := by simp [psiAt_eq, normEDS_one]
end GroundTheory.Arith.Abelian
