-- Prove2me | solution 1 for OAI.MetricKMedian.SparseBernoulli.count_failure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:44:52.517473+00:00
-- url     : https://prove2.me/submissions/dad0884d-008e-4551-b26f-71a1374734d3

import Mathlib
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseBernoulli_count_failure_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem _root_.solution (p a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {D P B t : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P) (ht : 0 < t)
    (hpP : ∀ i, (p i:ℝ) ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ B)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
    (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(p i:ℝ)) ≤
      -t-(1/2)*P^2*(D-1)*∑ i, (m i:ℝ)) :
    (run (d := 4) p hp n).real.prob (fun q => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) q) ≤
      (P*D^2*B*(∑ i, ((a i:ℝ)+(m i:ℝ))))/t^2 := by
  first
  | exact _root_.OAI.MetricKMedian.SparseBernoulli.count_failure_s35
  | (apply _root_.OAI.MetricKMedian.SparseBernoulli.count_failure_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.SparseBernoulli.count_failure_s35 <;> assumption)

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

