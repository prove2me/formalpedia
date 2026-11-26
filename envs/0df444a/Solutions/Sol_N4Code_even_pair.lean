-- Prove2me | solution 1 for N4Code.even_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:09.711912+00:00
-- url     : https://prove2.me/submissions/eaa865c1-9408-4aa8-8a3e-4bc9e6dbc618

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_odd_of_not_even
import Theorems.Thm_N4Code_hammingDist_mod2
import Theorems.Thm_N4Code_hammingDist_symm


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) : ∃ i j : Fin 4, i ≠ j ∧
    Even (hammingDist (row C i) (row C j)) := by
  by_cases h01 : Even (hammingDist (row C 0) (row C 1))
  · exact ⟨0, 1, by decide, h01⟩
  · by_cases h02 : Even (hammingDist (row C 0) (row C 2))
    · exact ⟨0, 2, by decide, h02⟩
    · -- d(0,1) and d(0,2) are odd → d(1,2) is even
      have h01o : Odd (hammingDist (row C 0) (row C 1)) := odd_of_not_even h01
      have h02o : Odd (hammingDist (row C 0) (row C 2)) := odd_of_not_even h02
      rcases h01o with ⟨a, h01a⟩
      rcases h02o with ⟨b, h02b⟩
      have hmod : hammingDist (row C 1) (row C 2) % 2 = 0 := by
        have h := hammingDist_mod2 (row C 1) (row C 0) (row C 2)
        have hsym : hammingDist (row C 1) (row C 0) = hammingDist (row C 0) (row C 1) :=
          hammingDist_symm _ _
        have hzero : (2 * a + 1 + (2 * b + 1)) % 2 = 0 := by
          have hsum : 2 * a + 1 + (2 * b + 1) = 2 * (a + b + 1) := by omega
          rw [hsum, Nat.mul_mod]
          norm_num
        rw [hsym, h01a, h02b, hzero] at h
        exact h
      have h12e : Even (hammingDist (row C 1) (row C 2)) := by
        have hdiv := Nat.div_add_mod (hammingDist (row C 1) (row C 2)) 2
        have hn : hammingDist (row C 1) (row C 2) = 2 * (hammingDist (row C 1) (row C 2) / 2) := by
          rw [hmod, add_zero] at hdiv
          rw [mul_comm] at hdiv
          calc
            hammingDist (row C 1) (row C 2) = hammingDist (row C 1) (row C 2) / 2 * 2 := hdiv.symm
            _ = 2 * (hammingDist (row C 1) (row C 2) / 2) := by rw [mul_comm]
        refine ⟨hammingDist (row C 1) (row C 2) / 2, ?_⟩
        have : 2 * (hammingDist (row C 1) (row C 2) / 2) =
            hammingDist (row C 1) (row C 2) / 2 + hammingDist (row C 1) (row C 2) / 2 := by rw [two_mul]
        rw [← this, ← hn]
      exact ⟨1, 2, by decide, h12e⟩
end N4Code
