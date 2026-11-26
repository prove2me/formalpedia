-- Prove2me | solution 1 for O3.aboveAP_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:12.673788+00:00
-- url     : https://prove2.me/submissions/744800ec-2f9f-4a20-bd3e-62895720e5d8

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : AboveTwoRegime p) :
    aboveAP p < 1 := by
  change 2 < p at hp
  have hpow : (2 : ℝ) ^ (2 - p) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [aboveAP, div_lt_one (by linarith)]
  linarith
end O3
