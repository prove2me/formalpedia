-- Prove2me | solution 1 for GlobalTheory.T.monic_coeff_natDegree_sub_eq_mul_cmConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:07.747797+00:00
-- url     : https://prove2.me/submissions/37b2f5c4-bf46-4fbb-adb6-69b509cef6c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicCoeffNatDegreeSubEqMulCmConj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicCoeffNatDegreeSubEqMulCmConjStatement
import Theorems.Thm_GlobalTheory_monic_coeff_natDegree_sub_eq_mul_complexConj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by
  first | exact @GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj | exact GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj | (intros; apply GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj <;> assumption)
end _root_.GlobalTheory.T
