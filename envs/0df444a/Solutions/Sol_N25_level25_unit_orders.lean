-- Prove2me | solution 1 for N25.level25_unit_orders
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:24.445036+00:00
-- url     : https://prove2.me/submissions/7efd6a46-e301-4f2d-bab6-11deddc2e5c7

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_subgroup_membership

set_option autoImplicit false

namespace N25

/-- The labels two and seven generate the claimed cyclic groups; the first four
positive powers of two are outside the level subgroup. -/
theorem _root_.solution :
    (2 : ZMod 25) ^ 5 = 7 ∧ (7 : ZMod 25)^2 = -1 ∧
    (2 : ZMod 25)^20 = 1 ∧
    (∀ n : Fin 20, n ≠ 0 → (2 : ZMod 25)^n.val ≠ 1) ∧
    ((ZMod.unitOfCoprime 2 (by decide))^5 ∈ H25) ∧
    (∀ n : Fin 5, n ≠ 0 → (ZMod.unitOfCoprime 2 (by decide))^n.val ∉ H25) := by
  refine ⟨by decide, by decide, by decide, by decide +kernel, ?_, ?_⟩
  · rw [level25_subgroup_membership]
    decide
  · intro n hn
    rw [level25_subgroup_membership]
    have h : ∀ n : Fin 5, n ≠ 0 →
        ¬ ((2 : ZMod 25)^n.val = 1 ∨ (2 : ZMod 25)^n.val = 7 ∨
          (2 : ZMod 25)^n.val = 18 ∨ (2 : ZMod 25)^n.val = 24) := by decide +kernel
    exact h n hn

end N25
