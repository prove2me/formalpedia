-- Prove2me | solution 1 for GlobalTheory.T.ae_polynomial_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:21.179726+00:00
-- url     : https://prove2.me/submissions/1746c67e-dfc2-482f-91b5-0421300e3855

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishing
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_AePoly_ae_eval_matrix_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M n : ℕ) (Q : MvPolynomial (Fin M × Fin n) ℂ), Q ≠ 0 → ∀ᵐ C ∂(volume : Measure (Fin M → Fin n → ℂ)), MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero | exact GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero | (intros; apply GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero <;> assumption)
end _root_.GlobalTheory.T
