-- Prove2me | solution 1 for GlobalTheory.T.exists_det_ne_zero_of_separating_functionals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:48:52.753712+00:00
-- url     : https://prove2.me/submissions/d55bb04c-f649-4a02-86b2-de01080d0092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetNeZeroOfRowsSeparating
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetNeZeroOfRowsSeparatingStatement
import Theorems.Thm_GlobalTheory_exists_det_ne_zero_of_rows_separating


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K), (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) → ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  first | exact @GlobalTheory.exists_det_ne_zero_of_rows_separating | exact GlobalTheory.exists_det_ne_zero_of_rows_separating | (intros; apply GlobalTheory.exists_det_ne_zero_of_rows_separating <;> assumption)
end _root_.GlobalTheory.T
