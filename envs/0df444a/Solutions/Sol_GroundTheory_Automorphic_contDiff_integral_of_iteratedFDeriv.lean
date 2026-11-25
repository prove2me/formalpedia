-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:19.193171+00:00
-- url     : https://prove2.me/submissions/39f9c027-c80d-4205-a155-71832da619f0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_integral_iter
import Theorems.Thm_GroundTheory_Automorphic_iteratedFDeriv_integral_eq

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
open ParamIntegral
namespace GroundTheory.Automorphic
theorem _root_.solution (F : P → α → F')
    (hF : ∀ a, ContDiff ℝ ∞ (fun Y => F Y a))
    (hcont : ∀ k : ℕ, Continuous (fun p : P × α => iter F k p.1 p.2))
    (hsupp : ∀ Y₀ : P, ∃ U ∈ 𝓝 Y₀, ∃ C : Set α, IsCompact C ∧ ∀ Y ∈ U, ∀ a ∉ C, F Y a = 0) :
    ContDiff ℝ ∞ (fun Y => ∫ a, F Y a ∂μ) := by
  refine contDiff_of_differentiable_iteratedFDeriv fun k _ => ?_
  rw [iteratedFDeriv_integral_eq F hF hcont hsupp k]
  exact fun Y => (hasFDerivAt_integral_iter F hF hcont hsupp k Y).differentiableAt
end GroundTheory.Automorphic
