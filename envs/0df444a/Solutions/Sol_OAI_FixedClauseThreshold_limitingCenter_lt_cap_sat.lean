-- Prove2me | solution 1 for OAI.FixedClauseThreshold.limitingCenter_lt_cap_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:55:27.03148+00:00
-- url     : https://prove2.me/submissions/375efa72-1f91-44d9-86dc-b77f795e226d

import Mathlib
import Definitions.Def_OAIQ067A002
import Theorems.Thm_OAI_FixedClauseThreshold_limitingCenter_bounds_sat

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Main
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
For every fixed clause size at least three, the proper-clause satisfiability
probability has a positive finite limiting threshold. No conclusion is asserted
at the critical density.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem limitingCenter_lt_cap_sat_oai (k : ℕ) (hk : 3 ≤ k) : limitingCenter k < capMultiplier k := by
  have hp : (1 : ℝ) < 2^k := one_lt_pow₀ (by norm_num) (by omega : k ≠ 0)
  have he : (capMultiplier k : ℝ) = 2^k * 2 := by simp [capMultiplier, pow_succ]
  rw [he]
  have h := (limitingCenter_bounds_sat k hk).2
  linarith

end


end FixedClauseThreshold

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.limitingCenter_lt_cap_sat_oai := @OAI.FixedClauseThreshold.limitingCenter_lt_cap_sat_oai
