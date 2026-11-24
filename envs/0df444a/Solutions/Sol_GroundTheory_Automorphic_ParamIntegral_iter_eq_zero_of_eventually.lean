-- Prove2me | solution 1 for GroundTheory.Automorphic.ParamIntegral.iter_eq_zero_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:45.349786+00:00
-- url     : https://prove2.me/submissions/0fc47635-cab1-4c7b-a3c3-b7e93be83f1a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Metric
open scoped ContDiff
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {α : Type*} [TopologicalSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
open GroundTheory.Automorphic.ParamIntegral
variable (F : P → α → F')
variable {F}
namespace GroundTheory.Automorphic.ParamIntegral
theorem _root_.solution {k : ℕ} {Y : P} {a : α} (h : ∀ᶠ Y' in 𝓝 Y, F Y' a = 0) :
    iter F k Y a = 0 := by
  have : (fun Y' => F Y' a) =ᶠ[𝓝 Y] fun _ => (0 : F') := h
  rw [iter, (this.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
  simp
end GroundTheory.Automorphic.ParamIntegral
