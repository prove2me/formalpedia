-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuation_coordinateRing_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:20.017801+00:00
-- url     : https://prove2.me/submissions/da0f6ebf-c68f-4465-a9e4-976e05ea2bc9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_smul_basis
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_poly_le_one
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_genY_le_one

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
variable {W}
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) (a : W.toAffine.CoordinateRing) :
    w (algebraMap _ W.toAffine.FunctionField a) ≤ 1 := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  rw [algebraMap_smul_basis]
  refine w.map_add_le (valuation_poly_le_one w hF hx p) ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (valuation_poly_le_one w hF hx q) (valuation_genY_le_one w hF hx)
end GroundTheory.Arith.Abelian
