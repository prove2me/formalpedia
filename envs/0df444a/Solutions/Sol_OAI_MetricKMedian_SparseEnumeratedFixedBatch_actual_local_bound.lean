-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:43:15.228718+00:00
-- url     : https://prove2.me/submissions/9f20f4ba-4d8d-478c-bc07-6490c6de6cc8

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedFixedBatch_actual_local_bound_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedFixedBatch
open Finset PhysicalPotential Analytic FixedBatch
variable {I : Type} [DecidableEq I] [Fintype I] {n : ℕ}

theorem _root_.solution (G : I → Finset I) (H S F : Finset I) (Δ : ℕ)
    (enum : Fin n ≃ HeavyAction (graphActions G) H)
    (p : ℚ) (q : HeavyAction (graphActions G) H → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1) {x g h φ R b b' : ℝ} (d : I → ℝ)
    (hprob : (p:ℝ)=2*h*g)
    (hG : ∀ i, (G i).card=Δ) (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*(p:ℝ))
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hy : mass g S ≤ 1) (hF : F ⊆ S) (hHS : H ∩ S ⊆ F)
    (hd0 : ∀ i, 0 ≤ d i) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S, d i ≤ R)
    (hbQ : b ≤ 5*((PhysicalPotential.cost g d S+(1-mass g S)*b)/g))
    (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) (hb'0 : 0 ≤ b') (hb' : b' ≤ b)
    (hbF : ∀ i ∈ F, b' ≤ d i) (hbH : ∀ i ∈ H, b' ≤ d i) :
    let D := heavyActions (graphActions G) H
    let μ := (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ)
      p q hp hq0).real
    μ.expect (fun A => potential (x*Real.exp (-h)) g d
      (nextAliveAt D (coefficient x (mass g S)) d (S \ F) A)
      (nextCap D d b' A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S e))+
      batchConstant Δ*h*(φ+h)*R := by
  first
  | exact _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s35
  | (apply _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s35 <;> assumption)

end MetricKMedian.SparseEnumeratedFixedBatch
end
end

end OAI
end

