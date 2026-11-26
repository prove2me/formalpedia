-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49ProgressiveV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:40:47.691856+00:00
-- url     : https://prove2.me/submissions/5c8de66b-bc8b-4b75-b1b4-5e88da471318

import Mathlib
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (ha : ∀ t, Measurable[F t] (X t)) :
    IsStronglyProgressive F X := by
  intro s
  let Z : NNReal → Ω → ℝ := fun t w => X (min t s) w
  have hz : ∀ t, Measurable[F s] (Z t) :=
    fun t => (ha (min t s)).mono (F.mono (min_le_right _ _)) le_rfl
  have hzr (w : Ω) (t : NNReal) : ContinuousWithinAt (fun u => Z u w) (Ici t) t := by
    exact (hr w (min t s)).comp
      (f := fun u : NNReal => min u s)
      (continuous_id.min continuous_const).continuousWithinAt
      (fun u hu => show min t s ≤ min u s from min_le_min (show t ≤ u from hu) le_rfl)
  have hZ := @AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation Ω (F s) Z hz hzr
  have hp : @Measurable (Iic s × Ω) (NNReal × Ω)
      (@Prod.instMeasurableSpace (Iic s) Ω inferInstance (F s))
      (@Prod.instMeasurableSpace NNReal Ω inferInstance (F s))
      (fun z => ((z.1 : NNReal),z.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hh := hZ.comp hp
  have he : (fun z : Iic s × Ω => Z (z.1 : NNReal) z.2) =
      (fun z : Iic s × Ω => X (z.1 : NNReal) z.2) := by
    funext z
    simp [Z,min_eq_left (show (z.1 : NNReal) ≤ s from z.1.property)]
  rw [← he]
  exact hh.stronglyMeasurable
