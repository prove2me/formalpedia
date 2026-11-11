-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:20:53.314005+00:00
-- url     : https://prove2.me/submissions/8666dde8-c959-4718-8c2c-95fca1133f15

import Mathlib
import Definitions.Def_Q238K014
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_advance_pos_lower_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma iterate_pos_s238_oai {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (t : ℕ) :
    (realMatrix (iterate D rows S t).shape).PosDef := by
  induction t with
  | zero => exact hS
  | succ t ih => exact (advance_pos_lower_s238 D hD rows _ hn ih).1

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238_oai := @OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238_oai
