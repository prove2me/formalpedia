-- Prove2me | solution 1 for KingmanSubadditive.BanachAlgebra.positive_part_finite
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:13:33.356793+00:00
-- url     : https://prove2.me/submissions/941296cc-50d4-42b2-9e73-26d8787e40b3

import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process



namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

theorem measurable_path_core {Ω : Type*} [MeasurableSpace Ω] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) : Measurable (path x) := by
  rw [measurable_pi_iff]
  intro p
  exact hmeas _ _ p.2

theorem measurable_shiftedPath_core {Ω : Type*} [MeasurableSpace Ω] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) : Measurable (shiftedPath x) := by
  rw [measurable_pi_iff]
  intro p
  exact hmeas _ _ (by have := p.2; omega)

/-- transport of the positive part along one shift -/
theorem shift_lintegral_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) (hmeas : IsMeasurableFamily x) (h2 : S2 P x)
    (s t : ℕ) (hst : s < t) :
    ∫⁻ ω, ENNReal.ofReal (x (s + 1) (t + 1) ω) ∂P = ∫⁻ ω, ENNReal.ofReal (x s t ω) ∂P := by
  let p : KingmanSubadditive.Ergodic.Interval := ⟨(s, t), hst⟩
  let g : (KingmanSubadditive.Ergodic.Interval → ℝ) → ENNReal :=
    fun φ => ENNReal.ofReal (φ p)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp (measurable_pi_apply p)
  have e1 : ∫⁻ ω, ENNReal.ofReal (x (s + 1) (t + 1) ω) ∂P
      = ∫⁻ φ, g φ ∂(Measure.map (shiftedPath x) P) := by
    rw [lintegral_map hg (measurable_shiftedPath_core x hmeas)]
    rfl
  have e2 : ∫⁻ ω, ENNReal.ofReal (x s t ω) ∂P
      = ∫⁻ φ, g φ ∂(Measure.map (path x) P) := by
    rw [lintegral_map hg (measurable_path_core x hmeas)]
    rfl
  rw [e1, e2, h2]

theorem positive_part_finite_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x) :
    ∀ s t : ℕ, s < t → ∫⁻ ω, ENNReal.ofReal (x s t ω) ∂P < ⊤ := by
  have step1 : ∀ r : ℕ, ∫⁻ ω, ENNReal.ofReal (x r (r + 1) ω) ∂P < ⊤ := by
    intro r
    induction r with
    | zero => exact h3'
    | succ r ih =>
      rw [shift_lintegral_core P x hmeas h2 r (r + 1) (by omega)]
      exact ih
  have key : ∀ k s : ℕ, ∫⁻ ω, ENNReal.ofReal (x s (s + k + 1) ω) ∂P < ⊤ := by
    intro k
    induction k with
    | zero => intro s; simpa using step1 s
    | succ k ih =>
      intro s
      have hae := h1 s (s + k + 1) (s + k + 2) (by omega) (by omega)
      have hle : ∫⁻ ω, ENNReal.ofReal (x s (s + (k + 1) + 1) ω) ∂P ≤
          ∫⁻ ω, (ENNReal.ofReal (x s (s + k + 1) ω) + ENNReal.ofReal (x (s + k + 1) (s + k + 2) ω)) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hae] with ω hω
        have : s + (k + 1) + 1 = s + k + 2 := by omega
        rw [this]
        exact le_trans (ENNReal.ofReal_le_ofReal hω) ENNReal.ofReal_add_le
      refine lt_of_le_of_lt hle ?_
      have hm : Measurable (fun ω => ENNReal.ofReal (x s (s + k + 1) ω)) :=
        ENNReal.measurable_ofReal.comp (hmeas s (s + k + 1) (by omega))
      rw [lintegral_add_left hm]
      exact ENNReal.add_lt_top.2 ⟨ih s, step1 (s + k + 1)⟩
  intro s t hst
  obtain ⟨k, rfl⟩ : ∃ k, t = s + k + 1 := ⟨t - s - 1, by omega⟩
  exact key k s

end KingmanSubadditive.BanachAlgebra

open KingmanSubadditive.BanachAlgebra
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x) :
    ∀ s t : ℕ, s < t → ∫⁻ ω, ENNReal.ofReal (x s t ω) ∂P < ⊤ := by
  exact positive_part_finite_core P x hmeas h1 h2 h3'
