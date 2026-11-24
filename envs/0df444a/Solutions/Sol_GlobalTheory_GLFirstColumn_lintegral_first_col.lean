-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.lintegral_first_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:21.102619+00:00
-- url     : https://prove2.me/submissions/c1e5aa3c-596a-4f35-bdef-ab157da85a8f

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
theorem _root_.solution {n k : ℕ} (F : (Fin n → Fin (k + 1) → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ x : Fin n → ℂ, ∫⁻ Y : Fin n → Fin k → ℂ, F fun a => Fin.cons (x a) (Y a) := by
  have h1 := volume_preserving_pi (ι := Fin n) (α' := fun _ => ℂ × (Fin k → ℂ))
    (β' := fun _ => Fin (k + 1) → ℂ) (fun _ => measurePreserving_cons ℂ k)
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow ℂ (Fin k → ℂ) (Fin n)).symm
  have h3 := h1.comp h2
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  exact lintegral_prod _ (hF.comp h3.measurable).aemeasurable
end GlobalTheory.GLFirstColumn
