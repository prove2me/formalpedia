-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_valid
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:55:15.030999+00:00
-- url     : https://prove2.me/submissions/aaf7fca6-9e2d-4cc1-99c9-f4290fa870cd

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_valid_s35


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


variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype J] [DecidableEq J] in
theorem solution (d₀ : F → F → ℚ) (location : F → X) (client : J → X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (R : J → ℝ) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hSA : ∀ j, S₀ j⊆A)
    (hR : ∀ j, 0≤R j) (hm : ∀ j, mass (g:ℝ) (S₀ j)=1)
    (hdR : ∀ j i, i∈S₀ j → dist (client j) (location i.1)≤R j)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    CopyState.Valid (g:ℝ) location client R S₀
      (z.1.1, replay g β x (fun j f => dist (client j) (location f)) S₀ z) := by
  exact OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s35 d₀ location client hd₀ g β p φ P hp hφ hupper A S₀ R T x hg hunit hP hP1 hA hSA hR hm hdR a
