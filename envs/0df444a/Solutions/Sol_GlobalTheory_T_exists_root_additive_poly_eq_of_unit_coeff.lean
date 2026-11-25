-- Prove2me | solution 1 for GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:58.383805+00:00
-- url     : https://prove2.me/submissions/e8c18c95-714c-49e8-aca4-133a4ba4186c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OntoOCAdditivePoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OntoOCAdditivePolyStatement
import Theorems.Thm_GlobalTheory_onto_OC_additive_poly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  first | exact @GlobalTheory.onto_OC_additive_poly | exact GlobalTheory.onto_OC_additive_poly | (intros; apply GlobalTheory.onto_OC_additive_poly <;> assumption)
end _root_.GlobalTheory.T
