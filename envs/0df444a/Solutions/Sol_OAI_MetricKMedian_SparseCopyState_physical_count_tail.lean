-- Prove2me | solution 1 for OAI.MetricKMedian.SparseCopyState.physical_count_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:43:48.792121+00:00
-- url     : https://prove2.me/submissions/4091c964-d77e-41ca-926f-0f83ce640fd2

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseCopyState_physical_count_tail_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCopyState
open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic CopyState
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem _root_.solution (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    {g p : ℚ} {φ b : ℝ} (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hG : ∀ i, (G i).card=Δ) (hpp : 0 ≤ p ∧ p ≤ 1)
    (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ φ*(g:ℝ)) :
    let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
      (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
    (∀ e, (q e:ℝ)=bias m (p:ℝ) φ (heavyParent (graphActions G) H e)) →
    (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ) p q hpp hq).real.prob
      (fun Z => mass (g:ℝ) A+4/((g:ℝ)*b) < mass (g:ℝ) (next Δ A (roundErased A G H Z) (roundOpened A G H Z))) ≤
        96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ)) := by
  first
  | exact _root_.OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35
  | (apply _root_.OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35 <;> assumption)

end MetricKMedian.SparseCopyState
end
end

end OAI
end

