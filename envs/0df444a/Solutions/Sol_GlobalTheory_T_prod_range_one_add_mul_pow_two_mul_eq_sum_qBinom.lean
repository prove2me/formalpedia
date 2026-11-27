-- Prove2me | solution 1 for GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:44:57.748128+00:00
-- url     : https://prove2.me/submissions/ba43ecf5-1a81-4e09-afc3-bcf15b02a57c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QBinomialFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QBinomialFiniteStatement
import Theorems.Thm_GlobalTheory_JacobiTriple_QBinomial_qBinomial_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  first | exact @GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | exact GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | (intros; apply GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite <;> assumption)
end _root_.GlobalTheory.T
