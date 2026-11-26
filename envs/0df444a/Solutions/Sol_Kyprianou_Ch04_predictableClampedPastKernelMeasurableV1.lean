-- Prove2me | solution 1 for Kyprianou.Ch04.predictableClampedPastKernelMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:21:29.208563+00:00
-- url     : https://prove2.me/submissions/18cac0f6-072f-4ce0-8238-6913cceb899e

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- A predictable kernel, sampled with time clamped to a fixed horizon, is jointly past measurable. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration NNReal mΩ) (T : NNReal)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g) :
    Measurable[(F T).prod inferInstance]
      (fun p : Ω × (ℝ × ℝ) => g ((min p.2.1.toNNReal T,p.1),p.2.2)) := by
  letI : MeasurableSpace Ω := F T
  let u : Ω × (ℝ × ℝ) → Iic T :=
    fun p => ⟨min p.2.1.toNNReal T,show min p.2.1.toNNReal T ≤ T from min_le_right _ _⟩
  have hu : Measurable u :=
    ((continuous_real_toNNReal.measurable.comp (measurable_fst.comp measurable_snd)).min
      measurable_const).subtype_mk
  have hq : Measurable[F T |>.prod inferInstance, F.predictable]
      (fun p : Ω × (ℝ × ℝ) => (min p.2.1.toNNReal T,p.1)) :=
    (measurable_inclusion_predictable (𝓕 := F) (i := T)).comp (hu.prodMk measurable_fst)
  exact hg.comp (hq.prodMk (measurable_snd.comp measurable_snd))
