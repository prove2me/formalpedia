-- Prove2me | solution 1 for OAI.MetricKMedian.SparseFixedCount.actual_count_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:39:59.799363+00:00
-- url     : https://prove2.me/submissions/ffbd073d-8862-4de1-be46-c135e31f1976

import Mathlib
import Definitions.Def_OAIQ035K049
import Theorems.Thm_OAI_MetricKMedian_SparseFixedCount_actual_count_tail_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseFixedCount
open Finset PhysicalPotential SourceBalance CountGeometry CountStatistic FixedBatch
variable {I : Type} [Fintype I] [DecidableEq I]

theorem _root_.solution (G : I → Finset I) {Δ n : ℕ} {g : ℚ} {p φ b : ℝ}
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < p) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hsmall : 8*p*(Δ:ℝ) ≤ φ*(g:ℝ))
    (hlarge : 1 < b*amount (fun h => mass (g:ℝ) ((graphActions G).erase h))) :
    let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
      (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
    (∀ e, (q e:ℝ)=bias m p φ (heavyParent (graphActions G) H e)) →
    (SparseEnumeratedBernoulli.law enum q hq).real.prob (fun ω => 0 < statistic
      (fun e => countOpening D Δ e-mass (g:ℝ) (countErase D Δ e))
      (fun e f => (g:ℝ)*(overlap (countErase D Δ) e f:ℝ)) ω) ≤
      96*(Δ:ℝ)^2*b/(p*φ^2*(g:ℝ)) := by
  first
  | exact _root_.OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35
  | (apply _root_.OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35 <;> assumption)

end MetricKMedian.SparseFixedCount
end
end

end OAI
end

