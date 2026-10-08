-- Prove2me | solution 1 for KingmanSubadditive.BanachAlgebra.truncation_isSubadditive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:15:14.687782+00:00
-- url     : https://prove2.me/submissions/fe02d177-e306-41e9-96bd-5ccd16c17fe4

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

theorem truncation_isSubadditive_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x)
    (N : ℕ) (hN : 1 ≤ N) :
    IsSubadditiveProcess P (truncate x N) := by
  have hmeasT : IsMeasurableFamily (truncate x N) := by
    intro s t hst
    exact (hmeas s t hst).max measurable_const
  refine ⟨hmeasT, ?_, ?_, ?_⟩
  · -- S1
    intro s t u hst htu
    filter_upwards [h1 s t u hst htu] with ω hω
    simp only [truncate]
    apply max_le
    · exact le_trans hω (add_le_add (le_max_left _ _) (le_max_left _ _))
    · calc -(N : ℝ) * ((u : ℝ) - (s : ℝ))
          = -(N : ℝ) * ((t : ℝ) - (s : ℝ)) + -(N : ℝ) * ((u : ℝ) - (t : ℝ)) := by ring
        _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)
  · -- S2
    let F : (KingmanSubadditive.Ergodic.Interval → ℝ) → (KingmanSubadditive.Ergodic.Interval → ℝ) :=
      fun φ p => max (φ p) (-(N : ℝ) * (((p.1.2 : ℕ) : ℝ) - ((p.1.1 : ℕ) : ℝ)))
    have hF : Measurable F := by
      rw [measurable_pi_iff]
      intro p
      exact (measurable_pi_apply p).max measurable_const
    have e1 : shiftedPath (truncate x N) = F ∘ shiftedPath x := by
      funext ω p
      simp only [shiftedPath, truncate, F, Function.comp]
      push_cast
      ring_nf
    have e2 : path (truncate x N) = F ∘ path x := by
      funext ω p
      rfl
    unfold S2
    rw [e1, e2, ← Measure.map_map hF (measurable_shiftedPath_core x hmeas),
      ← Measure.map_map hF (measurable_path_core x hmeas), h2]
  · -- S3
    have hfin : ∀ t : ℕ, 1 ≤ t → ∫⁻ ω, ENNReal.ofReal (x 0 t ω) ∂P < ⊤ :=
      fun t ht => positive_part_finite_core P x hmeas h1 h2 h3' 0 t ht
    have hint : ∀ t : ℕ, 1 ≤ t → Integrable (truncate x N 0 t) P := by
      intro t ht
      refine ⟨(hmeasT 0 t ht).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      have hb : ∀ ω, ‖truncate x N 0 t ω‖ₑ ≤
          ENNReal.ofReal (x 0 t ω) + ENNReal.ofReal ((N : ℝ) * (t : ℝ)) := by
        intro ω
        rw [Real.enorm_eq_ofReal_abs]
        have hNt : (0 : ℝ) ≤ (N : ℝ) * (t : ℝ) := by positivity
        simp only [truncate]
        rcases le_or_gt 0 (x 0 t ω) with hx | hx
        · rw [abs_of_nonneg (le_trans hx (le_max_left _ _))]
          calc ENNReal.ofReal (max (x 0 t ω) (-(N : ℝ) * ((t : ℝ) - ((0 : ℕ) : ℝ))))
              ≤ ENNReal.ofReal (x 0 t ω + (N : ℝ) * (t : ℝ)) := by
                apply ENNReal.ofReal_le_ofReal
                apply max_le (by linarith)
                push_cast; nlinarith
            _ ≤ _ := ENNReal.ofReal_add_le
        · have : max (x 0 t ω) (-(N : ℝ) * ((t : ℝ) - ((0 : ℕ) : ℝ))) ≤ 0 := by
            apply max_le hx.le
            push_cast; nlinarith
          have h2' : -((N : ℝ) * (t : ℝ)) ≤ max (x 0 t ω) (-(N : ℝ) * ((t : ℝ) - ((0 : ℕ) : ℝ))) := by
            refine le_trans ?_ (le_max_right _ _)
            push_cast; nlinarith
          rw [abs_of_nonpos this]
          calc ENNReal.ofReal (-max (x 0 t ω) (-(N : ℝ) * ((t : ℝ) - ((0 : ℕ) : ℝ))))
              ≤ ENNReal.ofReal ((N : ℝ) * (t : ℝ)) := ENNReal.ofReal_le_ofReal (by linarith)
            _ ≤ _ := le_add_self
      refine lt_of_le_of_lt (lintegral_mono hb) ?_
      rw [lintegral_add_right _ measurable_const, lintegral_const]
      exact ENNReal.add_lt_top.2 ⟨hfin t ht, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
    refine ⟨hint, ⟨(N : ℝ), ?_⟩⟩
    intro t ht
    unfold KingmanSubadditive.Ergodic.mean
    have hc : ∫ ω, (-(N : ℝ) * (t : ℝ)) ∂P = -(N : ℝ) * (t : ℝ) := by
      simp
    rw [← hc]
    apply integral_mono (integrable_const _) (hint t ht)
    intro ω
    simp only [truncate]
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    push_cast; ring

end KingmanSubadditive.BanachAlgebra

open KingmanSubadditive.BanachAlgebra
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x)
    (N : ℕ) (hN : 1 ≤ N) :
    IsSubadditiveProcess P (truncate x N) := by
  exact truncation_isSubadditive_core P x hmeas h1 h2 h3' N hN
