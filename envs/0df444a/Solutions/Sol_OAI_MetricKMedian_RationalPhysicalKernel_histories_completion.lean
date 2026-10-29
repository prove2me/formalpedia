-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_completion
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T05:00:45.914025+00:00
-- url     : https://prove2.me/submissions/1c79a6f6-5852-416e-ba61-f888b942620a

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_completion_s35


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


variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

theorem solution (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hBA : ∀ c, B c⊆A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1≤R c)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    let O := completed d R B hB g β z;
    ((O.card:ℝ)≤ mass (g:ℝ) z.1.1) ∧
    (0<j → O.Nonempty) ∧
    (score d O:ℝ) ≤ ∑ c, (
      potential (x T) (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1))
        (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())
        (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ z.1.1))+
      5*(R c:ℝ)*mass (g:ℝ)
        (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())) := by
  exact OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s35 d₀ d location client hd₀ hd g β p φ P hp hφ hupper A B R hB T x hg hunit hP hP1 hA hBA hR hm hdR a
