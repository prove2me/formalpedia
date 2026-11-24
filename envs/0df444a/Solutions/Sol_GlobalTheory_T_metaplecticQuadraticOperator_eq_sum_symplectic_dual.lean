-- Prove2me | solution 1 for GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:43.048302+00:00
-- url     : https://prove2.me/submissions/cae9bd91-73d2-472f-b30c-21494a7c3447

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticQuadraticOperatorEqSumSymplecticDual
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticQuadraticOperatorEqSumSymplecticDualStatement
import Theorems.Thm_GlobalTheory_quad_eq_sum_symplDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by
  first | exact @GlobalTheory.quad_eq_sum_symplDual | exact GlobalTheory.quad_eq_sum_symplDual | (intros; apply GlobalTheory.quad_eq_sum_symplDual <;> assumption)
end _root_.GlobalTheory.T
