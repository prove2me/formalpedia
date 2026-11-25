-- Prove2me | solution 1 for NormOnePowProof.conj_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:24.400798+00:00
-- url     : https://prove2.me/submissions/0a3db377-662b-4628-bbb3-2700ae2286a1

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal
import Theorems.Thm_NormOnePowProof_conj_mul
import Theorems.Thm_NormOnePowProof_conj_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open NormOnePowProof
variable {E : Type} [Field E] [NumberField E]
namespace NormOnePowProof
theorem _root_.solution (c : E →+* E) (hc : ∀ x, c (c x) = x) {A B : Submodule (𝓞 E) E}
    (hB : ∀ x, x ∈ B ↔ c x ∈ A) : ∀ n : ℕ, ∀ x, x ∈ B ^ n ↔ c x ∈ A ^ n := by
  intro n
  induction n with
  | zero => simpa only [pow_zero] using conj_one c hc
  | succ n ih =>
    simp only [pow_succ]
    exact conj_mul c hc ih hB
end NormOnePowProof
