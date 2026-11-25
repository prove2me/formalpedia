-- Prove2me | solution 1 for GlobalTheory.T.det_sq_norm_eq_hermitian_block_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:22:35.524669+00:00
-- url     : https://prove2.me/submissions/f3d55c41-7565-4c48-9459-eb554154929f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetSqNormEqHermitianBlockFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetSqNormEqHermitianBlockFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_KWhit_norm_det_bottom_block_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ), ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ → tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) → g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det → ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 * (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq | exact GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq | (intros; apply GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq <;> assumption)
end _root_.GlobalTheory.T
