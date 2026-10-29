-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:59:02.146676+00:00
-- url     : https://prove2.me/submissions/be9747b4-5094-45cd-9d09-a5f48dfa3975

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_count_tail_s35


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


variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] in

theorem solution (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (histories d g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => if mass (g:ℝ) A+(T:ℝ)*(4/((g:ℝ)*(β:ℝ))) < mass (g:ℝ) z.1.1 then 1 else 0) ≤
      (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))) := by
  exact OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail_s35 d location hd g β p φ P hp0 hφ0 hupper A T hg hg1 hp hφ hφ1 hβ hunit hP hP1 hA hsmall
