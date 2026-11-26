-- Prove2me | solution 1 for Kyprianou.Ch04.localizedResidualZeroOfPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:51:46.138733+00:00
-- url     : https://prove2.me/submissions/ded40ce6-110c-4aa0-ba8c-3665562ccabc

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_strictMaskRightContinuous
import Theorems.Thm_Kyprianou_Ch04_denseBoundedPrimitiveZero
import Theorems.Thm_Kyprianou_Ch04_rightContinuousZeroPrimitive
import Theorems.Thm_Kyprianou_Ch04_boundedPrimitiveClockLipschitz
import Theorems.Thm_Kyprianou_Ch04_stoppedPrimitiveMartingaleZero
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- Countably many bounded stopped primitives identify the original density. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (g : ℝ → Ω → ℝ) (tau : ℕ → Ω → WithTop NNReal)
    (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (h : ∀ᵐ w ∂P, Measurable (fun r => g r w) ∧
      (∀ s : ℝ, 0 ≤ s → ContinuousWithinAt (fun r => g r w) (Ici s) s) ∧
      (∀ t : NNReal, ∃ n, (t : WithTop NNReal) < tau n w) ∧
      ∀ n : ℕ, ∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)),
        ‖if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0‖ ≤ C n)
    (hM : ∀ n, Martingale (fun (t : NNReal) w =>
      ∫ r in Icc (0 : ℝ) (t : ℝ),
        (if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0) ∂volume) F P) :
    ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → g s w = 0 := by
  let k := fun n r w => if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0
  have hkm (n : ℕ) (w : Ω) (hw : Measurable (fun r => g r w)) :
      Measurable (fun r => k n r w) :=
    Measurable.ite (measurableSet_lt continuous_real_toNNReal.measurable.withTop_coe
      measurable_const) hw measurable_const
  have hki (n : ℕ) : ∀ᵐ w ∂P, (∀ t : NNReal,
      IntegrableOn (fun r => k n r w) (Icc (0 : ℝ) (t : ℝ)) volume) ∧
      (∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)), ‖k n r w‖ ≤ C n) := by
    filter_upwards [h] with w hw
    refine ⟨fun t => ?_, hw.2.2.2 n⟩
    haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) (t : ℝ))) :=
      ⟨by simp [Real.volume_Icc]⟩
    exact (integrable_const (C n)).mono' (hkm n w hw.1).aestronglyMeasurable
      (ae_restrict_of_ae_restrict_of_subset (fun _ hr => hr.1) (hw.2.2.2 n))
  have hz (n : ℕ) := stoppedPrimitiveMartingaleZero P F (k n) (C n) (hC n) (hki n) (hM n)
  have hq : ∀ᵐ w ∂P, ∀ (n : ℕ) (q : ℕ),
      (∫ r in Icc (0 : ℝ) ((TopologicalSpace.denseSeq NNReal q : NNReal) : ℝ), k n r w ∂volume) = 0 := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro q
    exact hz n (TopologicalSpace.denseSeq NNReal q)
  filter_upwards [h,hq,ae_all_iff.mpr hki] with w hw hqw hkw
  intro s hs
  obtain ⟨n,hn⟩ := hw.2.2.1 s.toNNReal
  have hkright := strictMaskRightContinuous (fun r => g r w) (tau n w) hw.2.1
  have hprim := denseBoundedPrimitiveZero (fun r => k n r w) (C n)
    (hC n) (hkw n).1 (hkw n).2 (hqw n)
  have hzero := rightContinuousZeroPrimitive (fun r => k n r w) (hkm n w hw.1)
    (hkw n).1 hkright hprim s hs
  simpa only [k,if_pos hn] using hzero
