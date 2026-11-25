-- Prove2me | solution 1 for GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:18:25.962809+00:00
-- url     : https://prove2.me/submissions/756fe4a8-3649-4b87-bd09-a5494c448ee2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosDefQuadMargin
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosDefQuadMarginStatement
import Theorems.Thm_GlobalTheory_posDef_quad_margin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] (M : ι → ι → ℝ), (∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) → ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  first | exact @GlobalTheory.posDef_quad_margin | exact GlobalTheory.posDef_quad_margin | (intros; apply GlobalTheory.posDef_quad_margin <;> assumption)
end _root_.GlobalTheory.T
