-- Prove2me | solution 1 for GlobalTheory.RealWeil.inner_proj_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:07:14.493838+00:00
-- url     : https://prove2.me/submissions/edc3d2ce-0339-4a96-bad1-26d329ba3c5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_inner_left
import Theorems.Thm_GlobalTheory_RealWeil_inner_proj_right
import Theorems.Thm_GlobalTheory_RealWeil_conj_gau
import Theorems.Thm_GlobalTheory_RealWeil_gau_neg


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
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x y : H) :
    ⟪proj h x, y⟫_ℂ = ⟪x, proj h y⟫_ℂ := by
  rw [← inner_conj_symm, inner_proj_right, inner_proj_right, ← integral_conj,
    ← integral_neg_eq_self (fun u => gau u * ⟪x, ρ u y⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, conj_gau, inner_conj_symm, gau_neg, h.inner_left hJ]
end GlobalTheory.RealWeil
