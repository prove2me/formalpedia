-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.eq_valuationInfty_of_genX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:42.774253+00:00
-- url     : https://prove2.me/submissions/b7a15936-91be-4a9f-a871-46c669132167

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_smul_basis
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_poly_of_one_lt
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_genY_of_one_lt
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_norm_smul_basis_of_q_eq_zero
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_norm_smul_basis_of_p_eq_zero
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_norm_smul_basis_of_ne_zero
import Theorems.Thm_GroundTheory_Arith_Abelian_valuationInfty_algebraMap
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
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) = exp 2) : w = valuationInfty W := by
  obtain ⟨m, hm, hm3⟩ := valuation_genY_of_one_lt w hF two_pos hx
  have hm' : m = 3 := by linarith
  subst hm'
  have hA : ∀ a : W.toAffine.CoordinateRing,
      w (algebraMap _ W.toAffine.FunctionField a) =
        valuationInfty W (algebraMap _ W.toAffine.FunctionField a) := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rw [valuationInfty_algebraMap, valuationInftyCoord_apply W ha]
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
    rw [algebraMap_smul_basis]
    rcases eq_or_ne q 0 with rfl | hq
    · have hp : p ≠ 0 := by rintro rfl; simp at ha
      rw [natDegree_norm_smul_basis_of_q_eq_zero, map_zero, zero_mul, add_zero,
        valuation_poly_of_one_lt w hF two_pos hx hp]
      push_cast; ring_nf
    · have hwQy : w (algebraMap F[X] W.toAffine.FunctionField q * genY W) =
          exp (2 * (q.natDegree : ℤ) + 3) := by
        rw [Valuation.map_mul, valuation_poly_of_one_lt w hF two_pos hx hq, hm, ← exp_add]
        ring_nf
      rcases eq_or_ne p 0 with rfl | hp
      · rw [natDegree_norm_smul_basis_of_p_eq_zero hq, map_zero, zero_add, hwQy]
        push_cast; ring_nf
      · rw [natDegree_norm_smul_basis_of_ne_zero hp hq]
        have hwP := valuation_poly_of_one_lt w hF two_pos hx hp
        rcases lt_or_gt_of_ne (show (2 * p.natDegree : ℤ) ≠ 2 * q.natDegree + 3 by omega) with
          hlt | hlt
        · rw [Valuation.map_add_eq_of_lt_right _ (by rw [hwP, hwQy, exp_lt_exp]; linarith), hwQy,
            max_eq_right (by omega)]
          push_cast; ring_nf
        · rw [Valuation.map_add_eq_of_lt_left _ (by rw [hwP, hwQy, exp_lt_exp]; linarith), hwP,
            max_eq_left (by omega)]
          push_cast; ring_nf
  refine Valuation.ext fun f => ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
  dsimp only
  have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hspec := IsLocalization.mk'_spec W.toAffine.FunctionField a s
  have h1 := congrArg w hspec
  have h2 := congrArg (valuationInfty W) hspec
  rw [Valuation.map_mul, hA, hA] at h1
  rw [Valuation.map_mul] at h2
  have hvs : valuationInfty W (algebraMap _ W.toAffine.FunctionField
      (s : W.toAffine.CoordinateRing)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs)
  exact mul_right_cancel₀ hvs (h1.trans h2.symm)
end GroundTheory.Arith.Abelian
