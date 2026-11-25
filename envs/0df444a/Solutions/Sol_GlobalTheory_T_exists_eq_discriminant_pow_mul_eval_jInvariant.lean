-- Prove2me | solution 1 for GlobalTheory.T.exists_eq_discriminant_pow_mul_eval_jInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:58:07.104393+00:00
-- url     : https://prove2.me/submissions/c4fe50bd-c1fc-48b5-ae75-4d9f06356c96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqDiscriminantPowMulEvalJInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqDiscriminantPowMulEvalJInvariantStatement
import Theorems.Thm_GlobalTheory_QFam_exists_eq_DD_pow_mul_eval_jT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Subring ℂ) (N w : ℕ) (f : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → QAll (· ∈ R) N f → ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = DD τ ^ w * P.eval (jT τ) := by
  first | exact @GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT | exact GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT | (intros; apply GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT <;> assumption)
end _root_.GlobalTheory.T
