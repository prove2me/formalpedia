-- Prove2me | solution 1 for OAI.FixedClauseThreshold.limitingCenter_pos_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:55:49.001969+00:00
-- url     : https://prove2.me/submissions/e016aaf7-2e6d-4b9f-b962-1d599f20b113

import Mathlib
import Definitions.Def_OAIQ067A002
import Theorems.Thm_OAI_FixedClauseThreshold_limitingCenter_bounds_sat

section
-- module Solutions.OAIQ067_SAT.RandomSAT_CenterBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem smallDensity_pos : 0 < smallDensity := by unfold smallDensity; positivity

theorem lowerCenterBound_pos : 0 < lowerCenterBound := div_pos smallDensity_pos (by norm_num)

end


end FixedClauseThreshold

end OAI
end

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

theorem limitingCenter_pos_sat_oai (k : ℕ) (hk : 3 ≤ k) : 0 < limitingCenter k :=
  lowerCenterBound_pos.trans_le (limitingCenter_bounds_sat k hk).1

end


end FixedClauseThreshold

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.limitingCenter_pos_sat_oai := @OAI.FixedClauseThreshold.limitingCenter_pos_sat_oai
