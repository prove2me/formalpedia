-- Prove2me | solution 1 for OAI.Laughlin.Spin.relativeHighestNorm_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:07:34.826539+00:00
-- url     : https://prove2.me/submissions/358dbf9a-e84e-413e-8223-8cfef5e5aea1

import Mathlib
import Definitions.Def_OAIQ050L015
import Theorems.Thm_OAI_Laughlin_Spin_relativeHighest_tendsto_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_HighestCouplingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem relativeHighestNorm_tendsto_s50_oai (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b)) (z : ℕ) :
    Tendsto (fun n => relativeHighestNorm (A n) (B n) z) atTop
      (𝓝 (oscillatorRelativeNorm (Real.sqrt (b/(1-b))) z)) := by
  apply Tendsto.sqrt
  apply tendsto_finsetSum
  intro p hp
  exact (relativeHighest_tendsto_s50 A B b hA hB hb0 hb1 hfrac z p
    (by have := Finset.mem_range.mp hp; omega)).pow 2

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.relativeHighestNorm_tendsto_s50_oai := @OAI.Laughlin.Spin.relativeHighestNorm_tendsto_s50_oai
