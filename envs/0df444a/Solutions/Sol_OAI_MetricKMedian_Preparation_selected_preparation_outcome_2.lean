-- Prove2me | solution 2 for OAI.MetricKMedian.Preparation.selected_preparation_outcome
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T05:02:19.292987+00:00
-- url     : https://prove2.me/submissions/0d1e85c2-caaa-4ccf-b326-828a56886b89

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_selected_preparation_outcome_s35


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


attribute [instance] CoupledLaw.finite
variable {I T J X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype J] [Nonempty J] [PseudoMetricSpace X]

theorem solution (F : T → Finset I) (Fj : J → Finset I) (y : I → ℝ)
    (s : T → X) (j : J → X) (i : I → X) (V : T → ℝ) (v : J → ℝ) (rep : J → T)
    {M δ T₁ g γ : ℝ} {Δ : ℕ}
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a ≤ 1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) (hT : 0 < T₁)
    (hθ : 1/(M*δ) ≤ 1/8) (hα : M/(δ*T₁) ≤ 1/4)
    (hg : 0 < g) (hγ : 0 < γ) ( hx1  : γ ≤ 1) ( hx2  : Even Δ) (hunit : g*(Δ:ℝ)=1)
    (hfail : failureFactor γ g < 1)
    (hsunit : ∀ t, ∑ a ∈ F t, y a=1)
    (hjunit : ∀ c, ∑ a ∈ Fj c, y a=1)
    ( hx3  : ∀ t, ∑ a ∈ F t, y a*dist (s t) (i a)=V t)
    (hjcost : ∀ c, ∑ a ∈ Fj c, y a*dist (j c) (i a)=v c)
    (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, dist (s t) (i a) ≤ dist (s t) (i b))
    ( hx4  : ∀ t u, t ≠ u → M*max (V t) (V u) < dist (s t) (s u))
    (hrepV : ∀ c, V (rep c) ≤ v c) (hrepD : ∀ c, dist (j c) (s (rep c)) ≤ M*v c)
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c
      g γ (∑ a, y a) Δ) :
    ∃ z : L.Ω × (T → Finset I), 0 < (L.ν.joint L.κ).weight z ∧
    ∃ r : J → Physical I T → ℝ,
      let n := physicalCount L z;
      (∀ a, n a ≤ Δ) ∧
      1 ≤ ∑ a, g*(n a:ℝ) ∧ (∑ a, g*(n a:ℝ)) ≤ (∑ a, y a)+3*g ∧
      (∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ g*(n a:ℝ)) ∧ (∑ a, r c a)=1) ∧
      (∑ c, ∑ a, r c a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)) ≤
        (max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
        (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ g)/(1-failureFactor γ g))*(∑ c, v c) := by
  exact OAI.MetricKMedian.Preparation.selected_preparation_outcome_s35 F Fj y s j i V v rep hy hy1 hM hδ hδ1 hT hθ hα hg hγ hx1 hx2 hunit hfail hsunit hjunit hx3 hjcost hnearest hx4 hrepV hrepD G L
