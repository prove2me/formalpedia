-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.gaussInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:45.479709+00:00
-- url     : https://prove2.me/submissions/377c335d-b20f-4929-86e5-c2f64970a6fe

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) := by
  intro ι _ c hc
  have h1 : MeasureTheory.Integrable (fun x : ℝ => Real.exp (-c * x ^ 2)) :=
    integrable_exp_neg_mul_sq hc
  have h2 := MeasureTheory.Integrable.fintype_prod (ι := ι) (f := fun _ x => Real.exp (-c * x ^ 2))
    (μ := fun _ => MeasureTheory.volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]
end GlobalTheory.CompanionTheory.EisTube
