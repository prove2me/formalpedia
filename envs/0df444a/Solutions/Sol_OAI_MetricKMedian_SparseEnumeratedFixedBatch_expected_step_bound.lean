-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:41:37.52408+00:00
-- url     : https://prove2.me/submissions/8f8eada0-3bb1-4beb-b718-3b3f17452ee6

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedFixedBatch_expected_step_bound_s35

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
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1) {h g φ : ℝ} {N : ℕ}
    (hprob : (p:ℝ)=2*h*g) (hh : 0 ≤ h) (hg : 0 ≤ g)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*(p:ℝ))
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    {x R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
    (SparseEnumeratedBatch.law enum Z C p q hp hq0).real.expect
      (fun A => potential (x*Real.exp (-h)) g d (nextAlive D x g d S A)
        (nextCap D d bForce A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+g*(∑ e ∈ relevant D S, charge D x g b d S e))+
      R*(16*((relevant D S).card:ℝ)*(N:ℝ)*h^2*g^2+
        8*((relevant D S).card:ℝ)*φ*h*g+
        256*((univ : Finset (relevant D S)).offDiag.card:ℝ)*h^2*g^2+
        6*h^2+8*((relevant D S).card:ℝ)*h^2*g) := by
  first
  | exact _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s35
  | (apply _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s35 <;> assumption)

end MetricKMedian.SparseEnumeratedFixedBatch
end
end

end OAI
end

