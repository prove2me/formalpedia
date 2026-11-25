-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFDerivAt_integral_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:22.687643+00:00
-- url     : https://prove2.me/submissions/dd4d4a22-0972-4eb6-a279-5dd4e77b92d3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Theorems.Thm_GroundTheory_Automorphic_ParamIntegral_iter_eq_zero_of_eventually
import Theorems.Thm_GroundTheory_Automorphic_ParamIntegral_fderiv_iter

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
set_option synthInstance.maxHeartbeats 200000
namespace GroundTheory.Automorphic
theorem _root_.solution (F : P → α → F')
    (hF : ∀ a, ContDiff ℝ ∞ (fun Y => F Y a))
    (hcont : ∀ k : ℕ, Continuous (fun p : P × α => iter F k p.1 p.2))
    (hsupp : ∀ Y₀ : P, ∃ U ∈ 𝓝 Y₀, ∃ C : Set α, IsCompact C ∧ ∀ Y ∈ U, ∀ a ∉ C, F Y a = 0)
    (k : ℕ) (Y₀ : P) :
    HasFDerivAt (fun Y => ∫ a, iter F k Y a ∂μ)
      (∫ a, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F'
        (iter F (k + 1) Y₀ a) ∂μ) Y₀ := by
  obtain ⟨U, hU, C, hC, hFC⟩ := hsupp Y₀
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU

  have hzero : ∀ j : ℕ, ∀ Y ∈ ball Y₀ r, ∀ a ∉ C, iter F j Y a = 0 := by
    intro j Y hY a ha
    refine iter_eq_zero_of_eventually ?_
    filter_upwards [isOpen_ball.mem_nhds hY] with Y' hY'
    exact hFC Y' (hrU hY') a ha
  have hcpt : ∀ j : ℕ, ∀ Y : P, Y ∈ ball Y₀ r → HasCompactSupport (iter F j Y) := fun j Y hY =>
    HasCompactSupport.intro hC fun a ha => hzero j Y hY a ha
  have hcY : ∀ j : ℕ, ∀ Y : P, Continuous (iter F j Y) := fun j Y =>
    (hcont j).comp (Continuous.prodMk_right Y)

  have hK : IsCompact (closedBall Y₀ (r / 2) ×ˢ C) := (isCompact_closedBall Y₀ _).prod hC
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont (k + 1)).continuousOn
  have hsub : ball Y₀ (r / 2) ⊆ ball Y₀ r := ball_subset_ball (by linarith)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := C.indicator fun _ => M)
    (F' := fun Y a => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F'
      (iter F (k + 1) Y a)) (ball_mem_nhds Y₀ (half_pos hr))
    (Eventually.of_forall fun Y => (hcY k Y).aestronglyMeasurable)
    ((hcY k Y₀).integrable_of_hasCompactSupport (hcpt k Y₀ (mem_ball_self hr)))
    ((LinearIsometryEquiv.continuous _).comp (hcY (k + 1) Y₀)).aestronglyMeasurable ?_ ?_ ?_
  · refine Eventually.of_forall fun a Y hY => ?_
    rw [LinearIsometryEquiv.norm_map]
    by_cases ha : a ∈ C
    · rw [indicator_of_mem ha]
      exact hM (Y, a) ⟨ball_subset_closedBall hY, ha⟩
    · rw [indicator_of_notMem ha, hzero (k + 1) Y (hsub hY) a ha, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)
  · refine Eventually.of_forall fun a Y _ => ?_
    rw [← fderiv_iter]
    have hd : Differentiable ℝ (fun Y => iter F k Y a) :=
      (hF a).differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
    exact (hd Y).hasFDerivAt
end GroundTheory.Automorphic
