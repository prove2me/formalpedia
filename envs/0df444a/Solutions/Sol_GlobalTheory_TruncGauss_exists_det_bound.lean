-- Prove2me | solution 1 for GlobalTheory.TruncGauss.exists_det_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:58.987648+00:00
-- url     : https://prove2.me/submissions/71d6d12d-c296-4d37-8f87-e454dbbd2bd8

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
import Theorems.Thm_GlobalTheory_TruncGauss_isCompact_bdd

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
open GlobalTheory GlobalTheory.TruncGauss
namespace GlobalTheory.TruncGauss
theorem _root_.solution (n : ℕ) (C : ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) → ‖H.det‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_bdd n C).exists_bound_of_continuousOn
    (continuous_id.matrix_det).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun H hH => (hK H hH).trans (le_max_left _ _)⟩
end GlobalTheory.TruncGauss
