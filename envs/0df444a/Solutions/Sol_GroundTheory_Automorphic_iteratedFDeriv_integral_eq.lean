-- Prove2me | solution 1 for GroundTheory.Automorphic.iteratedFDeriv_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:42.6694+00:00
-- url     : https://prove2.me/submissions/7402720f-e334-41f7-be79-f635824f0507

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_integral_iter

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
    (hsupp : ∀ Y₀ : P, ∃ U ∈ 𝓝 Y₀, ∃ C : Set α, IsCompact C ∧ ∀ Y ∈ U, ∀ a ∉ C, F Y a = 0)
    (k : ℕ) :
    iteratedFDeriv ℝ k (fun Y => ∫ a, F Y a ∂μ) = fun Y => ∫ a, iter F k Y a ∂μ := by
  induction k with
  | zero =>
    funext Y
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    simp only [iter, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ P F').symm.toContinuousLinearEquiv.integral_comp_comm
      (fun a => F Y a)).symm
  | succ k ih =>
    funext Y
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih,
      (hasFDerivAt_integral_iter F hF hcont hsupp k Y).fderiv]
    have e := LinearIsometry.integral_comp_comm (μ := μ) (𝕜 := ℝ)
      (E := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => P) F')
      (F := P →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F')
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F').toLinearIsometry
      (fun a => iter F (k + 1) Y a)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at e
    rw [e]
    simp
end GroundTheory.Automorphic
