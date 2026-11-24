-- Prove2me | solution 1 for GlobalTheory.T.haar_disintegration_averagedFibreMeasures
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:11:55.126537+00:00
-- url     : https://prove2.me/submissions/f273d71d-9906-4dc9-a418-e216e89de038

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HaarDisintegrationAveragedFibreMeasures
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HaarDisintegrationAveragedFibreMeasuresStatement
import Theorems.Thm_GlobalTheory_QuadFibre_disintegration


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
theorem _root_.solution : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → (∀ c : K, ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ) → μ {x | q x = 0} = 0 → ∀ φ : V → ENNReal, Measurable φ → ∫⁻ x, φ x ∂μ = ∫⁻ t, ∫⁻ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t) ∂ν := by
  first | exact @GlobalTheory.QuadFibre.disintegration | exact GlobalTheory.QuadFibre.disintegration | (intros; apply GlobalTheory.QuadFibre.disintegration <;> assumption)
end _root_.GlobalTheory.T
