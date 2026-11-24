-- Prove2me | solution 1 for GlobalTheory.T.integrable_continuousOn_averagedFibreIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:15:02.016234+00:00
-- url     : https://prove2.me/submissions/aa41dfda-3486-45f1-9ea2-da43540afe18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegralStatement
import Theorems.Thm_GlobalTheory_QuadFibre_integrable_and_continuousOn_fibOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → (∀ t : K, t ≠ 0 → Integrable φ (GlobalTheory.QuadFibre.fibOf μ ν q U s t)) ∧ ContinuousOn (fun t => ∫ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  first | exact @GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | exact GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | (intros; apply GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf <;> assumption)
end _root_.GlobalTheory.T
