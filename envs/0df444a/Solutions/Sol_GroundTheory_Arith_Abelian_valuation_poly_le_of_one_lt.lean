-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuation_poly_le_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:35.538717+00:00
-- url     : https://prove2.me/submissions/9ff3e585-0220-449c-9d3d-c6ea050b8181

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_poly_of_one_lt
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
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable {W}
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) (p : F[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    w (algebraMap F[X] W.toAffine.FunctionField p) ≤ exp (n * k) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [valuation_poly_of_one_lt w hF hk0 hk hp, exp_le_exp]
    have : (p.natDegree : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
end GroundTheory.Arith.Abelian
