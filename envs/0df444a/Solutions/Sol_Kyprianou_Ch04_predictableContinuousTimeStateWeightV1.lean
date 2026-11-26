-- Prove2me | solution 1 for Kyprianou.Ch04.predictableContinuousTimeStateWeightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:27:28.441916+00:00
-- url     : https://prove2.me/submissions/1b0565f4-182e-4651-a238-93a814569b57

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A continuous deterministic time-state weight evaluated at a predictable state is predictable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (V : NNReal → Ω → ℝ) (hV : IsStronglyPredictable F V)
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Ici (0 : ℝ) ×ˢ univ)) :
    Measurable[F.predictable] (fun p : NNReal × Ω => f (p.1 : ℝ) (V p.1 p.2)) := by
  have ht : IsStronglyPredictable F (fun (t : NNReal) (_ : Ω) => (t : ℝ)) :=
    AvramDividend.Classical.avram_wave3_04_strongAdapted_leftContinuous_predictable
      (fun _ => stronglyMeasurable_const)
      (fun _ _ => NNReal.continuous_coe.continuousWithinAt)
  have hc : Continuous (fun p : NNReal × ℝ => f (p.1 : ℝ) p.2) :=
    hf.comp_continuous (NNReal.continuous_coe.comp continuous_fst |>.prodMk continuous_snd)
      (fun p => ⟨p.1.coe_nonneg,mem_univ _⟩)
  exact hc.measurable.comp
    ((show Measurable[F.predictable] (fun p : NNReal × Ω => p.1) from by
      have h := ht.measurable
      have he : Real.toNNReal ∘ Function.uncurry (fun (t : NNReal) (_ : Ω) => (t : ℝ)) =
          (fun p : NNReal × Ω => p.1) := by
        funext p
        exact Real.toNNReal_coe
      rw [← he]
      exact measurable_real_toNNReal.comp h).prodMk hV.measurable)
