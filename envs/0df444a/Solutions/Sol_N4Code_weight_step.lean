-- Prove2me | solution 1 for N4Code.weight_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:08.092884+00:00
-- url     : https://prove2.me/submissions/84c331d9-4077-4269-bfd4-1321455f79a6

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (x : ℕ) :
    weight n ε (x + 1) < weight n ε x := by
  by_cases hx : x < n
  · have hn : n - (x + 1) = n - x - 1 := by omega
    have hn' : n - x = (n - x - 1) + 1 := by omega
    have hεlt : ε < 1 - ε := by linarith
    have hpos1 : 0 < 1 - ε := by nlinarith [hε1]
    have hposE : 0 < ε ^ x := by positivity
    calc
      (1 - ε) ^ (n - (x + 1)) * ε ^ (x + 1)
          = (1 - ε) ^ (n - x - 1) * (ε ^ x * ε) := by rw [hn, pow_succ]
      _ = ((1 - ε) ^ (n - x - 1) * ε ^ x) * ε := by ring
      _ < ((1 - ε) ^ (n - x - 1) * ε ^ x) * (1 - ε) := by
            exact mul_lt_mul_of_pos_left hεlt (by positivity : 0 < (1 - ε) ^ (n - x - 1) * ε ^ x)
      _ = (1 - ε) ^ (n - x) * ε ^ x := by
            have hmul : ((1 - ε) ^ (n - x - 1) * ε ^ x) * (1 - ε) =
                ((1 - ε) ^ (n - x - 1) * (1 - ε)) * ε ^ x := by ring
            rw [hmul]
            rw [← pow_succ]
            rw [show (n - x - 1) + 1 = n - x by omega]
  · have hn1 : n - (x + 1) = 0 := by omega
    have hn2 : n - x = 0 := by omega
    have hεlt1 : ε < 1 := by nlinarith [hε1]
    calc
      (1 - ε) ^ (n - (x + 1)) * ε ^ (x + 1)
          = ε ^ (x + 1) := by rw [hn1, pow_zero, one_mul]
      _ < ε ^ x := by
            rw [pow_succ]
            calc
              ε ^ x * ε < ε ^ x * 1 := by
                    exact mul_lt_mul_of_pos_left hεlt1 (by positivity : 0 < ε ^ x)
              _ = ε ^ x := by rw [mul_one]
      _ = (1 - ε) ^ (n - x) * ε ^ x := by rw [hn2, pow_zero, one_mul]
end N4Code
