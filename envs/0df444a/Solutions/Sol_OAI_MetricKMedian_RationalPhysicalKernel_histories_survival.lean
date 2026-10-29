-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_survival
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:57:18.717646+00:00
-- url     : https://prove2.me/submissions/81c02f19-b42b-4648-bae1-6b96f8d3e4b2

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_survival_s35


set_option maxHeartbeats 1000000

open Finset OAI.MetricKMedian OAI.MetricKMedian.PhysicalPotential
open OAI.MetricKMedian.FixedBatch OAI.MetricKMedian.CopyState
open OAI.MetricKMedian.Analytic OAI.MetricKMedian.Completion.Rational
open OAI.MetricKMedian.Preparation OAI.MetricKMedian.Preparation.SupplierStars OAI.MetricKMedian.Preparation.RationalSplitting
open OAI.MetricKMedian.GeneratorAverage OAI.MetricKMedian.GraphComparison
open OAI.MetricKMedian.RationalPhysicalKernel OAI.MetricKMedian.FixedBatch.RationalParameters


set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {Δ : ℕ}

theorem solution (d₀ : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A S₀ : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (x : ℕ → ℝ) (d : F → ℝ) {h : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hA : 1 ≤ mass (g:ℝ) A)
    (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S₀ ⊆ A) :
    (histories d₀ g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => mass (g:ℝ) (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())) ≤
      (1-h/2)^T*mass (g:ℝ) S₀ := by
  exact OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s35 d₀ location hd g β p φ P hp0 hφ0 hupper A S₀ T x d hprob hg hunit hP hP1 hh0 hh1 hφ1 hA hsmall hSA
