-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.rational_conditional_round_drift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:46:28.917466+00:00
-- url     : https://prove2.me/submissions/3df01ca4-3d61-4dee-9951-80952fad2639

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_CopyState_rational_conditional_round_drift_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F : Type} [DecidableEq F] [Fintype F] {Δ n : ℕ}

theorem _root_.solution (A S S₀ : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (RationalBatchData.graph G)
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
    {x h R : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hSA : S ⊆ A) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd0 : ∀ f, 0 ≤ d f) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, d i.1 ≤ R)
    (hR : ∃ i ∈ S₀, R=d i.1) :
    let H := RationalBatchData.heavySet (RationalBatchData.graphMass G g) β
    let μ := RationalBatchData.proposal G Δ g β p φ hp hφ hupper enum
    μ.real.expect (fun Z => potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))-
      potential x g (fun i => d i.1) S (GroupCap.cap R d (integral Δ A))) ≤
    h*(timeRate x (mass g S)*PhysicalPotential.cost g (fun i => d i.1) S+
      (g:ℝ)*(∑ e ∈ relevant (graphActions G) (localSet A S),
        charge (graphActions G) x g (GroupCap.cap R d (integral Δ A))
          (fun i => d i.val.1) (localSet A S) e))+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  first
  | exact _root_.OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s35
  | (apply _root_.OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s35 <;> assumption)

end MetricKMedian.CopyState
end
end

end OAI
end

