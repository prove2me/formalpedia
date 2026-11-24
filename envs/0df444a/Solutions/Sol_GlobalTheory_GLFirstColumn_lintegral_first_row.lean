-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.lintegral_first_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:21.760686+00:00
-- url     : https://prove2.me/submissions/0de68f8f-5806-4128-ade5-4c6f1dfdf435

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
import Theorems.Thm_GlobalTheory_GLFirstColumn_measurePreserving_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution {n k : ℕ} (F : (Fin (n + 1) → Fin k → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ m : Fin n → Fin k → ℂ, ∫⁻ r : Fin k → ℂ, F (Fin.cons r m) := by
  have h3 := measurePreserving_cons (Fin k → ℂ) n
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  exact lintegral_prod_symm _ (hF.comp h3.measurable).aemeasurable
end GlobalTheory.GLFirstColumn
