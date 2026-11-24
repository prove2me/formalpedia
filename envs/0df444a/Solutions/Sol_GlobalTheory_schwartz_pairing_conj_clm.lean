-- Prove2me | solution 1 for GlobalTheory.schwartz_pairing_conj_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:44.127702+00:00
-- url     : https://prove2.me/submissions/fc747764-252b-4c24-9887-e02a3c6d7ec4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzInnerProductContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  intro V _ _ _ μ hμ w
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hg : Function.HasTemperateGrowth (fun x => starRingEnd ℂ (w x)) :=
    (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp w.hasTemperateGrowth
  refine ⟨(SchwartzMap.integralCLM ℂ μ).comp (SchwartzMap.smulLeftCLM ℂ (fun x => starRingEnd ℂ (w x))), ?_⟩
  intro u
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  congr 1
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, mul_comm]
end GlobalTheory
