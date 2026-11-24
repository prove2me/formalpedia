-- Prove2me | solution 1 for GlobalTheory.RealWeil.proj_eq_self_of_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:42:47.223018+00:00
-- url     : https://prove2.me/submissions/cbdf86a0-89dc-4d79-9e6d-86b95b0cc4f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
import Theorems.Thm_GlobalTheory_RealWeil_inner_proj_right
import Theorems.Thm_GlobalTheory_RealWeil_inner_proj_left
import Theorems.Thm_GlobalTheory_RealWeil_integral_gau_mul_gau
import Theorems.Thm_GlobalTheory_RealWeil_proj_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped InnerProductSpace Real
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → H →L[ℂ] H}
namespace GlobalTheory.RealWeil
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {v : H}
    (hv : ∀ a, ⟪v, ρ a v⟫_ℂ = gau a * ⟪v, v⟫_ℂ) : proj h v = v := by
  have h1 : ⟪v, proj h v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [inner_proj_right]
    simp only [hv, ← mul_assoc]
    rw [integral_mul_const, integral_gau_mul_gau, one_mul]
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ), inner_sub_left, inner_sub_right, inner_sub_right,
    inner_proj_left hJ, inner_proj_left hJ, proj_idem hJ, h1]
  ring
end GlobalTheory.RealWeil
