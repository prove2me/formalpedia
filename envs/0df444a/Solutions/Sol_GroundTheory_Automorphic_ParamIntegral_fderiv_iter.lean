-- Prove2me | solution 1 for GroundTheory.Automorphic.ParamIntegral.fderiv_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:54.491839+00:00
-- url     : https://prove2.me/submissions/187da437-ff72-4547-867b-4f28fda76354

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
theorem _root_.solution (k : ℕ) (Y : P) (a : α) :
    fderiv ℝ (fun Y => iter F k Y a) Y =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F' (iter F (k + 1) Y a) := by
  simp [iter, iteratedFDeriv_succ_eq_comp_left]
end GroundTheory.Automorphic.ParamIntegral
