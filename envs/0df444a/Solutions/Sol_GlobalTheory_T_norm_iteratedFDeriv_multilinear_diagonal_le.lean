-- Prove2me | solution 1 for GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:46.456184+00:00
-- url     : https://prove2.me/submissions/4a9dd380-1cc4-4c5c-b8fd-85e7b647d306

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivMultilinearDiagonalLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivMultilinearDiagonalLeStatement
import Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_diag_multilinear_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ) (i : ℕ) (y : E),
    ‖iteratedFDeriv ℝ i (fun y : E => f (fun _ => y)) y‖ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le | exact GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le | (intros; apply GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le <;> assumption)
end _root_.GlobalTheory.T
