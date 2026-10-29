-- Prove2me | solution 2 for OAI.MetricKMedian.RationalPhysicalKernel.step_drift
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:41:35.106014+00:00
-- url     : https://prove2.me/submissions/21cc3e71-1424-43d0-b7ea-4e47d2d54193

import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_step_drift_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Finset OAI.MetricKMedian OAI.MetricKMedian.PhysicalPotential
open OAI.MetricKMedian.FixedBatch OAI.MetricKMedian.CopyState
open OAI.MetricKMedian.RationalPhysicalKernel

set_option maxHeartbeats 1000000

theorem solution {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
    (d₀ : F → F → ℚ) (location : F → X) (client : X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ P : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (S S₀ : Finset (Copy (F := F) Δ))
    {x h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) s.1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |(P:ℝ)-Analytic.P x| ≤ ζ)
    (hactive : S ⊆ s.1) (hS : S ⊆ S₀) (hm₀ : mass (g:ℝ) S₀=1)
    (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
    (step d₀ g β p φ P hp hφ hupper s).expectation (fun t =>
      potential (x*Real.exp (-h)) (g:ℝ) (fun i => dist client (location i.1))
        (labels g β x (fun (_ : Unit) f => dist client (location f)) t (fun _ => S) ())
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ t.1))) ≤
      potential x (g:ℝ) (fun i => dist client (location i.1)) S
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ s.1))+
      h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S+
      batchConstant Δ*h*((φ:ℝ)+h)*R :=
  OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s35 d₀ location client hd₀ g β p φ P hp hφ hupper s S S₀ hprob hg hg1 hunit hP hP1 hA hx0 hx1 hh0 hh1 hφ1 hsmall hζ0 hζ1 he hactive hS hm₀ hR0 hdR hR

end
