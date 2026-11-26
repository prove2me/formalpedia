-- Prove2me | solution 1 for O3.aboveEta_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:14.521823+00:00
-- url     : https://prove2.me/submissions/9c5fdeaa-d9af-4dd8-bc2c-947a15b33916

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : AboveTwoRegime p) :
    aboveEta p < 1 := by
  change 2 < p at hp
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
end O3
