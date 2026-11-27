-- Prove2me | solution 1 for GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:06:16.062106+00:00
-- url     : https://prove2.me/submissions/dd1809c6-a780-4eee-8d26-62f2b3224e7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumEqSumOfMatchingFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumEqSumOfMatchingFamilyStatement
import Theorems.Thm_GlobalTheory_hasSum_eq_sum_of_matching_family


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  first | exact @GlobalTheory.hasSum_eq_sum_of_matching_family | exact GlobalTheory.hasSum_eq_sum_of_matching_family | (intros; apply GlobalTheory.hasSum_eq_sum_of_matching_family <;> assumption)
end _root_.GlobalTheory.T
