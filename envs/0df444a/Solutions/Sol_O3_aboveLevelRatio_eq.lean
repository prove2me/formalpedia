-- Prove2me | solution 1 for O3.aboveLevelRatio_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:08:58.090849+00:00
-- url     : https://prove2.me/submissions/e59e7aff-b94b-4c45-8c71-45482766a918

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {M D eps theta : ℝ}
    (hM : M ≠ 0) (heps : eps ≠ 0) (htheta : theta ≠ 0) :
    aboveInitialLevel M D /
        aboveTerminalLevel (theta * eps) M =
      8 * (aboveKappa M D eps) ^ 2 / theta ^ 2 := by
  unfold aboveInitialLevel aboveTerminalLevel aboveKappa
  field_simp [hM, heps, htheta]
end O3
