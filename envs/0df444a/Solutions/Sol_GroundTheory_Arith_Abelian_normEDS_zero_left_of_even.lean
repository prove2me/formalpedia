-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.normEDS_zero_left_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:04.885848+00:00
-- url     : https://prove2.me/submissions/757561ec-a2dd-4620-ab45-159ba9f71850

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints

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
variable {R : Type*} [CommRing R] [IsDomain R]
omit [IsDomain R]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (c d : R) {n : ℤ} (hn : Even n) : normEDS 0 c d n = 0 := by
  simp [normEDS, hn]
end GroundTheory.Arith.Abelian
