-- Prove2me | solution 1 for GlobalTheory.QuadFibre.exists_integrable_bound_unit_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:44:47.9428+00:00
-- url     : https://prove2.me/submissions/43bbbc2e-b32f-45ae-81ea-674b9161d86e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
theorem _root_.solution {K V : Type} [NormedField K] [ProperSpace K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] [ContinuousSMul K V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasureOnCompacts μ]
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ g : V → ℝ, Integrable g μ ∧ ∀ (a : K) (x : V), ‖a‖ = 1 → ‖φ (a • x)‖ ≤ g x := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set T : Set V := Metric.sphere (0 : K) 1 • tsupport φ with hTdef
  have hT : IsCompact T := by
    have := ((isCompact_sphere (0 : K) 1).prod hc).image (f := fun p : K × V => p.1 • p.2) continuous_smul
    rwa [Set.image_smul_prod] at this
  refine ⟨T.indicator (fun _ => C), ?_, ?_⟩
  · exact (integrable_indicator_iff hT.isClosed.measurableSet).mpr
      (integrableOn_const hT.measure_lt_top.ne)
  · intro a x ha
    by_cases hx : φ (a • x) = 0
    · rw [hx, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hC0) x
    · have ha0 : a ≠ 0 := by
        rintro rfl
        rw [norm_zero] at ha
        exact zero_ne_one ha
      have hmem : x ∈ T := by
        refine Set.mem_smul.mpr ⟨a⁻¹, ?_, a • x, subset_tsupport _ (Function.mem_support.mpr hx),
          inv_smul_smul₀ ha0 x⟩
        rw [mem_sphere_zero_iff_norm, norm_inv, ha, inv_one]
      rw [Set.indicator_of_mem hmem]
      exact hC _
end GlobalTheory.QuadFibre
