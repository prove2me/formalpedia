-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.nearby_assignments
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T05:04:02.747777+00:00
-- url     : https://prove2.me/submissions/b1ca62f1-1435-4e78-b952-8f0422613ec5

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_nearby_assignments_s35


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
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem solution (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ g γ B T₁ v p₀ : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hT₁ : 0 ≤ T₁)
    (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ G.p t)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hD : dist j (s t) ≤ M*v) (hL : 0 < G.c t → G.L t ≤ T₁*v)
    (hR : G.c t=0 → ∀ a ∈ F t, dist (s t) (i a) ≤ T₁*v) :
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        nearFactor p₀ (M+(1+δ)*T₁) γ g*v := by
  exact OAI.MetricKMedian.Preparation.nearby_assignments_s35 F y s i V G L hy hM hδ hT₁ hg hγ hunit hp₀ hp₀1 hp j t Fj hmj hvj hD hL hR
