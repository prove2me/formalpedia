-- Prove2me | solution 1 for N4Code.weight_pred_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:48.316806+00:00
-- url     : https://prove2.me/submissions/545a5e4a-7047-488a-8d23-f2a77b4d36ef

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} {ε : ℝ} (_hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    weight n ε (d - 1) - weight n ε d =
      (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by
  have hden : 1 - ε ≠ 0 := by linarith
  have hnsub : n - (d - 1) = n - d + 1 := by omega
  have hsum : n - d + 1 + (d - 1) = n := by omega
  have hpow : (1 - ε) ^ (n - (d - 1)) = (1 - ε) ^ (n - d) * (1 - ε) := by
    rw [hnsub, pow_succ]
  have hepow : ε ^ d = ε ^ (d - 1) * ε := by
    calc
      ε ^ d = ε ^ ((d - 1) + 1) := by
        congr 1
        omega
      _ = ε ^ (d - 1) * ε := by rw [pow_succ]
  calc
    weight n ε (d - 1) - weight n ε d
        = (1 - ε) ^ (n - d) * (1 - ε) * ε ^ (d - 1) - (1 - ε) ^ (n - d) * (ε ^ (d - 1) * ε) := by
          unfold weight
          rw [hpow, hepow]
    _ = (1 - ε) ^ (n - d) * ε ^ (d - 1) * ((1 - ε) - ε) := by ring
    _ = (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by
          calc
            (1 - ε) ^ (n - d) * ε ^ (d - 1) * ((1 - ε) - ε)
                = (1 - ε) ^ (n - d) * (1 - ε) * ε ^ (d - 1) * (1 - 2 * ε) / (1 - ε) := by
                  field_simp [hden]
                  ring
            _ = (1 - ε) ^ (n - (d - 1)) * ε ^ (d - 1) * (1 - 2 * ε) / (1 - ε) := by
                  rw [← hpow]
            _ = (1 - ε) ^ (n - d + 1) * ε ^ (d - 1) * (1 - 2 * ε) / (1 - ε) := by
                  rw [hnsub]
            _ = (1 - ε) ^ (n - d + 1) * (1 - ε) ^ (d - 1)
                    * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by
                  rw [div_pow]
                  field_simp [hden]
                  ring
            _ = (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by
                  rw [← pow_add, hsum]
end N4Code
