-- Prove2me | solution 1 for OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:50:37.97302+00:00
-- url     : https://prove2.me/submissions/f4a778fe-d86c-4194-9c02-ade390888764

import Mathlib
import Definitions.Def_OAIQ035K029
import Theorems.Thm_OAI_MetricKMedian_FiniteComparison_actual_scalar_bounds_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

open Analytic

theorem _root_.solution {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) :
    ScalarBounds (P x) (m x) (A x+2*P x*w) (P x*w^2) (Certificates.h (1-x)) (actualB x w) := by
  first
  | exact _root_.OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35
  | (apply _root_.OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35 <;> assumption)

end MetricKMedian.FiniteComparison

end
end

end OAI
end

