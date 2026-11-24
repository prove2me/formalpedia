-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuation_poly_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:27.06292+00:00
-- url     : https://prove2.me/submissions/573a91d5-8c91-4d1f-b634-75c0dd6f16d4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_C_functionField
import Theorems.Thm_GroundTheory_Arith_Abelian_genX_eq


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
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) {p : F[X]} (hp : p ≠ 0) :
    w (algebraMap F[X] W.toAffine.FunctionField p) = exp (p.natDegree * k) := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    have hlead : w (algebraMap F[X] W.toAffine.FunctionField
        (C p.leadingCoeff * X ^ p.natDegree)) = exp (d * k) := by
      rw [map_mul, map_pow, algebraMap_C_functionField, Valuation.map_mul, Valuation.map_pow,
        hF _ (leadingCoeff_ne_zero.mpr hp), ← genX_eq, hk, one_mul, ← exp_nsmul, h, nsmul_eq_mul]
    rw [← eraseLead_add_C_mul_X_pow p, map_add]
    rcases (eraseLead_natDegree_lt_or_eraseLead_eq_zero p) with hlt | he
    · by_cases he : p.eraseLead = 0
      · rw [he, map_zero, zero_add, hlead]
      · have hd : (p.eraseLead.natDegree : ℤ) < d := by exact_mod_cast h ▸ hlt
        rw [Valuation.map_add_eq_of_lt_right _ ?_, hlead]
        rw [hlead, ih _ (h ▸ hlt) he rfl, exp_lt_exp]
        nlinarith
    · rw [he, map_zero, zero_add, hlead]
end GroundTheory.Arith.Abelian
