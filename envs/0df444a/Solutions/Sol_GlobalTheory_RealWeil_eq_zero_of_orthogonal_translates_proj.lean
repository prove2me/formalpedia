-- Prove2me | solution 1 for GlobalTheory.RealWeil.eq_zero_of_orthogonal_translates_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:11.174801+00:00
-- url     : https://prove2.me/submissions/9ef08664-04e8-452a-ad88-58108ae20925

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_inner_left
import Theorems.Thm_GlobalTheory_RealWeil_inner_proj_left
import Theorems.Thm_GlobalTheory_RealWeil_Good_inversion


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
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {x : H}
    (hx : ∀ y a, ⟪ρ a (proj h y), x⟫_ℂ = 0) : x = 0 := by
  have h1 : ∀ a, proj h (ρ (-a) x) = 0 := fun a => by
    refine ext_inner_left ℂ fun y => ?_
    rw [← inner_proj_left hJ, ← h.inner_left hJ, hx, inner_zero_right]
  have hg : Good h x := fun n => by simp [h1]
  rw [← hg.inversion hJ]
  simp [h1]
end GlobalTheory.RealWeil
