-- Prove2me | solution 1 for GlobalTheory.T.product_hua_determinant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:29.469134+00:00
-- url     : https://prove2.me/submissions/46259217-76b2-4346-a57b-407614adf093

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductHuaDeterminantIntegrable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductHuaDeterminantIntegrableStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_integrable_prod_detW_rpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
  ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow <;> assumption)
end _root_.GlobalTheory.T
