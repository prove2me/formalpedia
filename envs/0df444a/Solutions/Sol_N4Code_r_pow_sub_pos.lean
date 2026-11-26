-- Prove2me | solution 1 for N4Code.r_pow_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:33.053188+00:00
-- url     : https://prove2.me/submissions/6ac6c9af-e4a8-4475-9f60-f1f65b500927

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_r_pos
import Theorems.Thm_N4Code_r_lt_one

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {d : ℕ} (hd : 1 ≤ d) :
    0 < (ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d := by
  have hr : ε / (1 - ε) < 1 := r_lt_one hε1
  have hpos : 0 < (ε / (1 - ε)) ^ (d - 1) := pow_pos (r_pos hε0 hε1) (d - 1)
  have h1r : 0 < 1 - ε / (1 - ε) := by linarith
  have hpow' : (ε / (1 - ε)) ^ d = (ε / (1 - ε)) ^ (d - 1) * (ε / (1 - ε)) := by
    calc
      (ε / (1 - ε)) ^ d = (ε / (1 - ε)) ^ ((d - 1) + 1) := by
        congr 1
        omega
      _ = (ε / (1 - ε)) ^ (d - 1) * (ε / (1 - ε)) := by rw [pow_succ]
  calc
    (ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d
        = (ε / (1 - ε)) ^ (d - 1) * (1 - ε / (1 - ε)) := by
          rw [hpow']
          ring
    _ > 0 := mul_pos hpos h1r
end N4Code
