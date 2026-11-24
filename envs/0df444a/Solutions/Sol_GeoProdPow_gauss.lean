-- Prove2me | solution 1 for GeoProdPow.gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:52:57.164395+00:00
-- url     : https://prove2.me/submissions/de485b41-b68e-4dcf-84a8-82ce4c3dc59d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeometricProductBound_OneSubSumLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GeoProdPow
open Finset
namespace GeoProdPow
theorem _root_.solution (r : ℕ) : ∑ i ∈ Ico 1 r, i = r * (r - 1) / 2 := by
  rcases r with _ | r
  · simp
  · rw [← Finset.sum_range_id, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos r)]
    simp
end GeoProdPow
