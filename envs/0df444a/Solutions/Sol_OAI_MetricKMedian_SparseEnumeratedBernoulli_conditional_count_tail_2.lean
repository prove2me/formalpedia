-- Prove2me | solution 2 for OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:40:33.823025+00:00
-- url     : https://prove2.me/submissions/f028c7ae-40cf-4258-89f9-f9b7dbcda316

import Mathlib
import Definitions.Def_OAIQ035K049
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBernoulli_conditional_count_tail_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBernoulli
open Finset
variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

theorem _root_.solution (enum : Fin n ≃ E) (q a m : E → ℚ) (c : E → E → ℚ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) {D p φ g A b : ℝ}
    (hD : 1 ≤ D) (hp : 0 < p) (hφ : 0 < φ) (hg : 0 < g) (hb : 0 < b)
    (hlarge : 1 < b*A) (hqP : ∀ i, (q i:ℝ) ≤ 2*p)
    (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ b*A+2)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
    (hmass : (∑ i, (m i:ℝ)) ≤ 2*A/g)
    (htotal : (∑ i, ((a i:ℝ)+(m i:ℝ))) ≤ 4*A/g)
    (hsmall : 8*p*D ≤ φ*g)
    (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(q i:ℝ)) ≤ -p*φ*A) :
    (law enum q hq).real.prob (fun ω => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
      96*D^2*b/(p*φ^2*g) := by
  first
  | exact _root_.OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail_s35
  | (apply _root_.OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail_s35 <;> assumption)

end MetricKMedian.SparseEnumeratedBernoulli
end
end

end OAI
end

