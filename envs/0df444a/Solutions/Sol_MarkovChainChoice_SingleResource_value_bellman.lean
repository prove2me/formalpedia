-- Prove2me | solution 1 for MarkovChainChoice.SingleResource.value_bellman
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:44:51.789981+00:00
-- url     : https://prove2.me/submissions/4c5cfd23-d4bb-4c3d-a26b-ca2a6a0b6d89

import Definitions.Def_MarkovChainChoice_SingleResource_ValueFunction
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Tactic
open Finset MarkovChainChoice.Shared MarkovChainChoice.SingleResource

theorem solution {n : ℕ} (M : Model n) (r : Fin n → ℝ) (T : ℕ) :
    (∀ x, value M r T (T + 1) x = 0) ∧
      (∀ t, 1 ≤ t → t ≤ T → value M r T t 0 = 0) ∧
      ∀ t x, 1 ≤ t → t ≤ T → 1 ≤ x →
        value M r T t x =
          (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty (fun S =>
            ∑ j, purchase M S j * (r j + value M r T (t + 1) (x - 1)) +
              (1 - ∑ j, purchase M S j) * value M r T (t + 1) x) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro x; simp [value,valueToGo]
  · intro t ht hT
    unfold value
    cases T+1-t <;> simp [valueToGo]
  · intro t x ht hT hx
    have htime : T+1-t = (T+1-(t+1))+1 := by omega
    have hcap : x = (x-1)+1 := by omega
    unfold value
    conv_lhs => rw [htime,hcap,valueToGo]
    rw [← hcap, sup'_add]
    apply sup'_congr univ_nonempty rfl
    intro S hS
    simp only [mul_sub,sum_sub_distrib,← sum_mul]
    ring
