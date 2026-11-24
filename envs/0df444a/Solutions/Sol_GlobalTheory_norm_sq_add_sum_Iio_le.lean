-- Prove2me | solution 1 for GlobalTheory.norm_sq_add_sum_Iio_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:20.656325+00:00
-- url     : https://prove2.me/submissions/22c8d1e9-ed91-415d-a4cf-7c411cbb1fec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution {n : ℕ} {v : Fin n → E} {i : Fin n} {r : ℝ}
    (h : ∀ j ≤ i, ‖v j‖ ≤ r) :
    ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 ≤ (((i : ℕ) + 1 + 3 : ℝ) / 4) * r ^ 2 := by
  have h1 : ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 ≤ (Finset.Iio i).card • r ^ 2 :=
    Finset.sum_le_card_nsmul _ _ _ fun j hj =>
      pow_le_pow_left₀ (norm_nonneg _) (h j (Finset.mem_Iio.1 hj).le) 2
  rw [Fin.card_Iio, nsmul_eq_mul] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (h i le_rfl) 2
  linarith
end GlobalTheory
