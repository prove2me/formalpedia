-- Prove2me | solution 1 for GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:21:13.788498+00:00
-- url     : https://prove2.me/submissions/e31d21e4-3cf3-4be0-9ce4-77b82922d99b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValuesStatement
import Theorems.Thm_GlobalTheory_submodule_pow_simple_eq_sum_equiv_values


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
theorem _root_.solution : ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧ y = ∑ l, Sm l (q l) := by
  first | exact @GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | exact GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | (intros; apply GlobalTheory.submodule_pow_simple_eq_sum_equiv_values <;> assumption)
end _root_.GlobalTheory.T
