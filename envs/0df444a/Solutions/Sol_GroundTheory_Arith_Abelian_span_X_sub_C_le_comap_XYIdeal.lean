-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.span_X_sub_C_le_comap_XYIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:32.994114+00:00
-- url     : https://prove2.me/submissions/54d6112d-d08e-4116-9fc6-2ea826b69346

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_X_sub_C

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
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (x : F) (y : F[X]) :
    Ideal.span {X - C x} ≤ (XYIdeal W.toAffine x y).comap (algebraMap F[X] _) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    algebraMap_X_sub_C]
  exact Ideal.subset_span (Set.mem_insert _ _)
end GroundTheory.Arith.Abelian
