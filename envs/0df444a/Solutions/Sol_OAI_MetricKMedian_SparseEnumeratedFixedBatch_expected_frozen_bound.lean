-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:42:11.218173+00:00
-- url     : https://prove2.me/submissions/69884263-feff-4ebc-932f-aa31c65c1ee3

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedFixedBatch_expected_frozen_bound_s35

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedFixedBatch
open Finset PhysicalPotential Analytic FixedBatch
variable {I E : Type} [DecidableEq I] [DecidableEq E] [Fintype E] {n : ℕ}

theorem _root_.solution (enum : Fin n ≃ E) (D : Actions I E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hQ : 0 ≤ Q)
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    {x g R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
    (SparseEnumeratedBatch.law enum Z C p q hp hq0).real.expect
      (fun A => potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b) ≤
      ((p:ℝ)/2)*(∑ e ∈ relevant D S, charge D x g b d S e)+
        ((relevant D S).card:ℝ)*(8*R)*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
        2*(8*R)*((univ : Finset (relevant D S)).offDiag.card:ℝ)*Q^2 := by
  first
  | exact _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s35
  | (apply _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s35 <;> assumption)

end MetricKMedian.SparseEnumeratedFixedBatch
end
end

end OAI
end

