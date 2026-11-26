-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryRationalDriftAtOriginV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:46:58.604117+00:00
-- url     : https://prove2.me/submissions/2ec7b131-761d-4bff-84b2-378843056bcc

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_levyJointMeasurableVersionV1
import Theorems.Thm_Kyprianou_Ch04_stationaryEventFubiniV1
import Theorems.Thm_Kyprianou_Ch04_stationaryRationalDriftEventV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Transfer a pathwise almost-everywhere rational slope limit to time zero. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (d : ℝ)
    (hA : ∀ᵐ ω ∂P, ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun r : ℚ =>
        (X (Real.toNNReal s + Real.toNNReal (r : ℝ)) ω - X (Real.toNNReal s) ω) /
          (Real.toNNReal (r : ℝ) : ℝ))
        (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun r : ℚ => X (Real.toNNReal (r : ℝ)) ω / (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d) := by
  obtain ⟨Z, hZm, hZ⟩ := Kyprianou.Ch04.levyJointMeasurableVersionV1 P X hX
  let Q := volume.restrict (Ioo (0 : ℝ) 1)
  have hQ : NeBot (ae Q) := by
    rw [ae_neBot]
    intro h
    have he : Q univ = 0 := by rw [h]; simp
    simpa [Q, Measure.restrict_apply, Real.volume_Ioo] using he
  let A : ℝ → Ω → Prop := fun s ω => Tendsto (fun r : ℚ =>
    (Z (Real.toNNReal s + Real.toNNReal (r : ℝ)) ω - Z (Real.toNNReal s) ω) /
      (Real.toNNReal (r : ℝ) : ℝ)) (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d)
  have hm : MeasurableSet {z : ℝ × Ω | A z.1 z.2} := by
    apply measurableSet_tendsto (nhds d)
    intro r
    have h1 : Measurable (fun z : ℝ × Ω =>
        (Real.toNNReal z.1 + Real.toNNReal (r : ℝ), z.2)) :=
      (measurable_fst.real_toNNReal.add measurable_const).prodMk measurable_snd
    have h2 : Measurable (fun z : ℝ × Ω => (Real.toNNReal z.1, z.2)) :=
      measurable_fst.real_toNNReal.prodMk measurable_snd
    exact ((hZm.comp h1).sub (hZm.comp h2)).div_const _
  have ha : ∀ᵐ ω ∂P, ∀ᵐ s ∂Q, A s ω := by
    filter_upwards [hA, hZ] with ω ha hz
    simpa only [A, hz] using ha
  have hst (s : ℝ) (hs : ∀ᵐ ω ∂P, A s ω) : ∀ᵐ ω ∂P, A 0 ω := by
    have hOrig := (Kyprianou.Ch04.stationaryRationalDriftEventV1 P X hX d (Real.toNNReal s)).mp
      (by filter_upwards [hs, hZ] with ω hs hz; simpa only [A, hz] using hs)
    filter_upwards [hOrig, hZ] with ω hω hz
    simpa [A, hz, hX.start_zero] using hω
  have h0 := Kyprianou.Ch04.stationaryEventFubiniV1 P Q hQ A hm ha hst
  filter_upwards [h0, hZ] with ω hω hz
  simpa [A, hz, hX.start_zero] using hω
