-- Prove2me | solution 1 for OAI.Problem337.egyptian_length_is_minimum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:01:11.182681+00:00
-- url     : https://prove2.me/submissions/0485f37a-cefb-4c0b-8969-70b8c9c03d56

import Mathlib
import Definitions.Def_EgyptianFractions

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_EgyptianExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Elementary greedy existence, stated independently of the shared definitions. -/
theorem exists_strict_unit_fraction_sum (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      (∀ i, 2 ≤ n i) ∧ StrictMono n ∧
      (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = (a : ℚ) / (b : ℚ) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    have ha0 : 0 < a := ha
    have hb0 : 0 < b := lt_trans ha0 hab
    have hdiv := Nat.div_add_mod b a
    have hmod := Nat.mod_lt b ha0
    by_cases hr : b % a = 0
    · have hq : 2 ≤ b / a := by
        by_contra h
        have hq' : b / a ≤ 1 := by omega
        have hmul : a * (b / a) ≤ a := by nlinarith
        omega
      refine ⟨1, fun _ => b / a, (fun _ => hq), ?_, ?_⟩
      · intro i j hij
        have hi := i.isLt
        have hj := j.isLt
        omega
      · simp only [Fin.sum_univ_one]
        have heq : a * (b / a) = b := by omega
        have hq0 : ((b / a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : b / a ≠ 0)
        have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
        have heq' : (a : ℚ) * (b / a : ℕ) = b := by exact_mod_cast heq
        apply (div_eq_div_iff hq0 hbq).2
        simpa [mul_comm] using heq'.symm
    · let d := b / a + 1
      let c := a - b % a
      have hd : 2 ≤ d := by
        have := Nat.div_pos (Nat.le_of_lt hab) ha0
        dsimp [d]
        omega
      have hd0 : 0 < d := by omega
      have hcpos : 1 ≤ c := by dsimp [c]; omega
      have hca : c < a := by dsimp [c]; omega
      have hcb : c < b * d := by nlinarith
      obtain ⟨k, n, hn, hmono, hsum⟩ := ih c hca (b * d) hcpos hcb
      have hbq : (0 : ℚ) < b := by exact_mod_cast hb0
      have hdq : (0 : ℚ) < d := by exact_mod_cast hd0
      have hdecomp : (1 : ℚ) / d + (c : ℚ) / (b * d : ℕ) = (a : ℚ) / b := by
        have hc : (c : ℚ) = a - (b % a : ℕ) := by
          dsimp [c]
          exact Nat.cast_sub (Nat.le_of_lt hmod)
        have hdivq : (a : ℚ) * (b / a : ℕ) + (b % a : ℕ) = b := by
          exact_mod_cast hdiv
        have hddef : (d : ℚ) = (b / a : ℕ) + 1 := by simp [d]
        push_cast
        field_simp
        nlinarith
      have hsmall : (c : ℚ) / (b * d : ℕ) < (1 : ℚ) / d := by
        have hcb' : (c : ℚ) < b := by exact_mod_cast (lt_trans hca hab)
        push_cast
        apply (div_lt_div_iff₀ (mul_pos hbq hdq) hdq).2
        nlinarith
      have hdn : ∀ i, d < n i := by
        intro i
        have hle : (1 : ℚ) / n i ≤ (c : ℚ) / (b * d : ℕ) := by
          rw [← hsum]
          exact Finset.single_le_sum (f := fun j : Fin k => (1 : ℚ) / n j) (fun j _ => by positivity) (Finset.mem_univ i)
        have hni : (0 : ℚ) < n i := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hn i))
        have := (one_div_lt_one_div hni hdq).1 (lt_of_le_of_lt hle hsmall)
        exact_mod_cast this
      refine ⟨k + 1, Fin.cons d n, ?_, ?_, ?_⟩
      · intro i
        exact Fin.cases hd (fun j => hn j) i
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact False.elim ((lt_irrefl _) hij)
          | succ j => simpa using hdn j
        | succ i =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j => simpa using hmono (Fin.succ_lt_succ_iff.mp hij)
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hsum]
        exact hdecomp

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LengthBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The least length is bounded by every witnessed length. -/
theorem egyptianLength_le_of_expansion {a b k : ℕ}
    (h : ∃ n : Fin k → ℕ, IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) :
    egyptianLength a b ≤ k := by
  exact csInf_le' h

/-- Existence is the only input needed to obtain a least expansion. -/
theorem egyptianLength_attained_of_exists {a b : ℕ}
    (h : ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) :
    ∃ n : Fin (egyptianLength a b) → ℕ,
      IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n := by
  exact Nat.sInf_mem h

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

theorem egyptian_length_is_minimum_oai :
    ∀ a b : ℕ, 1 ≤ a → a < b →
  (∃ n : Fin (egyptianLength a b) → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) ∧
  (∀ k : ℕ, (∃ n : Fin k → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) →
    egyptianLength a b ≤ k) := by
  intro a b ha hab
  constructor
  · exact egyptianLength_attained_of_exists (exists_strict_unit_fraction_sum a b ha hab)
  · intro k hk
    exact egyptianLength_le_of_expansion hk

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.egyptian_length_is_minimum_oai := @OAI.Problem337.egyptian_length_is_minimum_oai
