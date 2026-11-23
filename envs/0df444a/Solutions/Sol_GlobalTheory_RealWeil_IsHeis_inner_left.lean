-- Prove2me | solution 1 for GlobalTheory.RealWeil.IsHeis.inner_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:12.449354+00:00
-- url     : https://prove2.me/submissions/45b4bcb0-34ca-4876-bb32-c85375488e2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
import Theorems.Thm_GlobalTheory_RealWeil_omJ_skew


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
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace H]
namespace GlobalTheory.RealWeil
namespace IsHeis
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (u : V) (x y : H) :
    ⟪ρ u x, y⟫_ℂ = ⟪x, ρ (-u) y⟫_ℂ := by
  have h0 : omJ J u (-u) = 0 := by
    have := omJ_skew hJ u u
    have e : omJ J u (-u) = -omJ J u u := by simp [omJ]
    linarith
  have e : ρ u (ρ (-u) y) = y := by
    rw [h.2.1, h0, add_neg_cancel, h.1]
    simp
  have := (⟨(ρ u : H →ₗ[ℂ] H), h.2.2.1 u⟩ : H →ₗᵢ[ℂ] H).inner_map_map x (ρ (-u) y)
  rw [← this]
  change _ = ⟪ρ u x, ρ u (ρ (-u) y)⟫_ℂ
  rw [e]
end IsHeis
end GlobalTheory.RealWeil
