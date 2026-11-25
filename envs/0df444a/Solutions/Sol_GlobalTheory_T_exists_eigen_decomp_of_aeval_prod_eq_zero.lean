-- Prove2me | solution 1 for GlobalTheory.T.exists_eigen_decomp_of_aeval_prod_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:26.546793+00:00
-- url     : https://prove2.me/submissions/f3a46335-bfd0-4088-97a5-406413d287b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumEigenvectorsOfAevalProdLinearEqZero
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumEigenvectorsOfAevalProdLinearEqZeroStatement
import Theorems.Thm_GlobalTheory_sum_eigenvectors_of_aeval_prod_linear_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → Polynomial.aeval (-Ω) (∏ s, (Polynomial.X + Polynomial.C (ν s))) = 0 → ∀ w : N, ∃ v : Fin n → N, (∀ s, Ω (v s) = ν s • v s) ∧ w = ∑ s, v s := by
  first | exact @GlobalTheory.sum_eigenvectors_of_aeval_prod_linear_eq_zero | exact GlobalTheory.sum_eigenvectors_of_aeval_prod_linear_eq_zero | (intros; apply GlobalTheory.sum_eigenvectors_of_aeval_prod_linear_eq_zero <;> assumption)
end _root_.GlobalTheory.T
