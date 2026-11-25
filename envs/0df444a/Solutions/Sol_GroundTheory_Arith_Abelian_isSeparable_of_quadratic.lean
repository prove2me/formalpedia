-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.isSeparable_of_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:07.0738+00:00
-- url     : https://prove2.me/submissions/046762d5-aca3-4c98-9f15-dd0f46fdc72e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
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
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
universe u
variable {F : Type u} [Field F]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {L K : Type*} [Field L] [Field K] [Algebra L K] {y : K} (b c : L)
    (hy : y ^ 2 + algebraMap L K b * y - algebraMap L K c = 0)
    (hD' : algebraMap L K b ^ 2 + 4 * algebraMap L K c ≠ 0) :
    IsSeparable L y := by
  have hD : b ^ 2 + 4 * c ≠ 0 := fun h => hD' (by
    rw [← map_pow, ← map_ofNat (algebraMap L K) 4, ← map_mul, ← map_add, h, map_zero])
  have hq' : derivative (X ^ 2 + C b * X - C c : L[X]) = C 2 * X + C b := by
    simp only [derivative_sub, derivative_add, derivative_X_pow, derivative_C_mul_X, derivative_C]
    simp
  have hsep : (X ^ 2 + C b * X - C c : L[X]).Separable := by
    rw [Polynomial.separable_def, hq']
    refine ⟨C (-4 * (b ^ 2 + 4 * c)⁻¹), C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b), ?_⟩
    have e : (C 2 * X + C b) ^ 2 - 4 * (X ^ 2 + C b * X - C c) = C (b ^ 2 + 4 * c) := by
      simp only [map_add, map_pow, map_mul, map_ofNat]; ring
    calc C (-4 * (b ^ 2 + 4 * c)⁻¹) * (X ^ 2 + C b * X - C c) +
          C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b) * (C 2 * X + C b)
        = C (b ^ 2 + 4 * c)⁻¹ * ((C 2 * X + C b) ^ 2 - 4 * (X ^ 2 + C b * X - C c)) := by
          simp only [map_mul, map_neg, map_ofNat]; ring
      _ = 1 := by rw [e, ← C_mul, inv_mul_cancel₀ hD, C_1]
  have hq : aeval y (X ^ 2 + C b * X - C c : L[X]) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
    exact hy
  exact hsep.of_dvd (minpoly.dvd L y hq)
end GroundTheory.Arith.Abelian
