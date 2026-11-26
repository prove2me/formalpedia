-- Prove2me | solution 1 for O3.aboveGamma_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:20.865677+00:00
-- url     : https://prove2.me/submissions/aeca7c8e-e5b5-49bf-baf8-851aaa6cc5d2

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p B : ℝ} {n : ℕ}
    (_hp : AboveTwoRegime p) (hn : 1 ≤ n) (hB : 0 < B) :
    0 < aboveGamma p n B := by
  unfold aboveGamma
  exact mul_pos
    (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _)
    (Real.rpow_pos_of_pos hB _)
end O3
