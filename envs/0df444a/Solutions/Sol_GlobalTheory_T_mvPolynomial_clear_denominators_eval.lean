-- Prove2me | solution 1 for GlobalTheory.T.mvPolynomial_clear_denominators_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:03.486575+00:00
-- url     : https://prove2.me/submissions/a1302108-c258-4db5-943d-91e9af591128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEval
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEvalStatement
import Theorems.Thm_GlobalTheory_clearDenominators


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
theorem _root_.solution : ∀ {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K) (P D : ι → MvPolynomial τ K), ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) → MvPolynomial.eval y M ≠ 0 ∧ MvPolynomial.eval y G = MvPolynomial.eval y M * MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  first | exact @GlobalTheory.clearDenominators | exact GlobalTheory.clearDenominators | (intros; apply GlobalTheory.clearDenominators <;> assumption)
end _root_.GlobalTheory.T
