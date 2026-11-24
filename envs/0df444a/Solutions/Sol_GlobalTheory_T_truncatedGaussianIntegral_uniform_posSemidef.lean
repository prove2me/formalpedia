-- Prove2me | solution 1 for GlobalTheory.T.truncatedGaussianIntegral_uniform_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:23:16.063368+00:00
-- url     : https://prove2.me/submissions/da1a25b4-9680-45fa-9409-e3edfc1b220d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidefStatement
import Theorems.Thm_GlobalTheory_TruncGauss_trunc_gauss


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (C ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosSemidef → (∀ j l, ‖H j l‖ ≤ C) → 1 ≤ (H.det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) := by
  first | exact @GlobalTheory.TruncGauss.trunc_gauss | exact GlobalTheory.TruncGauss.trunc_gauss | (intros; apply GlobalTheory.TruncGauss.trunc_gauss <;> assumption)
end _root_.GlobalTheory.T
