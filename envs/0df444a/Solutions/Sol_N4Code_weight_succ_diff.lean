-- Prove2me | solution 1 for N4Code.weight_succ_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:15.771539+00:00
-- url     : https://prove2.me/submissions/8052dbd9-e43b-4923-bd4b-3e4a94062d07

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_weight_pred_diff

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} {ε : ℝ} (_hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {d : ℕ} (hdn : d < n) :
    weight n ε (d + 1) - weight n ε d =
      -((1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ d) := by
  have h := weight_pred_diff (n := n) (ε := ε) _hε0 hε1 (d := d + 1) (by omega) (by omega)
  have hsub : d + 1 - 1 = d := by omega
  rw [hsub] at h
  linarith
end N4Code
