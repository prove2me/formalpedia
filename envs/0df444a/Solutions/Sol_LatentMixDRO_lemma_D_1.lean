-- Prove2me | solution 1 for LatentMixDRO.lemma_D_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T05:45:29.640944+00:00
-- url     : https://prove2.me/submissions/17f39ac8-fcbf-4315-ad54-cea68763d78e

import Mathlib

open MeasureTheory

set_option maxHeartbeats 800000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → ℝ) (hW : Integrable W μ) (α₀ : ℝ) (hα₀ : 0 < α₀) (hα₀' : α₀ < 1 / 2) :
    ∃ v : ℝ,
      IsLUB {s | ∃ 𝓛 : Ω → ℝ, Measurable 𝓛 ∧ (∀ a, 0 ≤ 𝓛 a ∧ 𝓛 a ≤ 1 / α₀) ∧
        (∫ a, 𝓛 a ∂μ) = 1 ∧ s = ∫ a, 𝓛 a * W a ∂μ} v ∧
      IsGLB {s | ∃ η : ℝ, s = (1 / α₀) * (∫ a, max (W a - η) 0 ∂μ) + η} v := by
  classical
  obtain ⟨W', hW'strong, hW'ae⟩ := hW.aestronglyMeasurable
  have hW'meas : Measurable W' := hW'strong.measurable
  have hW'int : Integrable W' μ := hW.congr hW'ae
  have hα₁ : 1 < 1 / α₀ := by rw [lt_div_iff₀ hα₀]; linarith
  have main : ∀ (V : Ω → ℝ), Measurable V → Integrable V μ → ∃ v : ℝ,
      IsLUB {s | ∃ 𝓛 : Ω → ℝ, Measurable 𝓛 ∧ (∀ a, 0 ≤ 𝓛 a ∧ 𝓛 a ≤ 1 / α₀) ∧
        (∫ a, 𝓛 a ∂μ) = 1 ∧ s = ∫ a, 𝓛 a * V a ∂μ} v ∧
      IsGLB {s | ∃ η : ℝ, s = (1 / α₀) * (∫ a, max (V a - η) 0 ∂μ) + η} v := by
    intro V hVmeas hVint
    have hHint : ∀ η : ℝ, Integrable (fun a => max (V a - η) 0) μ := by
      intro η
      have h1 : Integrable (fun a => V a - η) μ := hVint.sub (integrable_const η)
      refine Integrable.mono' (g := fun a => |V a - η|) h1.abs ?_ ?_
      · have hs : AEStronglyMeasurable (fun a : Ω => V a - η) μ :=
          hVmeas.aestronglyMeasurable.sub aestronglyMeasurable_const
        have h0 : AEStronglyMeasurable (fun a : Ω => (0 : ℝ)) μ := aestronglyMeasurable_const
        exact hs.sup h0
      · filter_upwards with a
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self (V a - η)) (abs_nonneg _)
    let G : ℝ → ℝ := fun η => ∫ a, max (V a - η) 0 ∂μ
    let ψ : ℝ → ℝ := fun η => (1 / α₀) * G η + η
    have hG_nonneg : ∀ η, 0 ≤ G η := by
      intro η
      exact integral_nonneg (fun a => le_max_right _ _)
    have hG_ge : ∀ η, ∫ a, V a ∂μ - η ≤ G η := by
      intro η
      have h1 : ∫ a, (V a - η) ∂μ = ∫ a, V a ∂μ - η := by
        rw [integral_sub hVint (integrable_const η)]
        simp
      show ∫ a, max (V a - η) 0 ∂μ ≥ ∫ a, V a ∂μ - η
      rw [← h1]
      exact integral_mono_ae (hVint.sub (integrable_const η)) (hHint η)
        (Filter.Eventually.of_forall (fun a => le_max_left _ _))
    have hG_lip : ∀ η η' : ℝ, |G η - G η'| ≤ |η - η'| := by
      intro η η'
      have hsub : G η - G η' = ∫ a, (max (V a - η) 0 - max (V a - η') 0) ∂μ := by
        show (∫ a, max (V a - η) 0 ∂μ) - (∫ a, max (V a - η') 0 ∂μ) = _
        rw [integral_sub (hHint η) (hHint η')]
      rw [hsub]
      calc |∫ a, (max (V a - η) 0 - max (V a - η') 0) ∂μ|
          ≤ ∫ a, |max (V a - η) 0 - max (V a - η') 0| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ a, |η - η'| ∂μ := by
            apply integral_mono_ae
            · exact ((hHint η).sub (hHint η')).abs
            · exact integrable_const _
            · filter_upwards with a
              have h := abs_max_sub_max_le_abs (V a - η) (V a - η') 0
              rw [show (V a - η) - (V a - η') = -(η - η') from by ring, abs_neg] at h
              exact h
        _ = |η - η'| := by simp
    have hψcont : Continuous ψ := by
      have hGcont : Continuous G := by
        refine LipschitzWith.continuous (K := 1) ?_
        rw [lipschitzWith_iff_dist_le_mul]
        intro x y
        rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
        exact hG_lip x y
      exact (continuous_const.mul hGcont).add continuous_id
    set c : ℝ := 1 / α₀ - 1 with hcdef
    have hcpos : 0 < c := by rw [hcdef]; linarith
    let R : ℝ := max 1 (max (ψ 0) ((ψ 0 - (1 / α₀) * ∫ a, V a ∂μ) / c + 1))
    have hR1 : 1 ≤ R := le_max_left _ _
    have hRψ : ψ 0 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
    have hRq : (ψ 0 - (1 / α₀) * ∫ a, V a ∂μ) / c + 1 ≤ R :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hRc : ψ 0 - (1 / α₀) * ∫ a, V a ∂μ ≤ R * c := by
      have h1 : (ψ 0 - (1 / α₀) * ∫ a, V a ∂μ) / c ≤ R := by linarith
      have h2 : ((ψ 0 - (1 / α₀) * ∫ a, V a ∂μ) / c) * c ≤ R * c :=
        mul_le_mul_of_nonneg_right h1 hcpos.le
      calc ψ 0 - (1 / α₀) * ∫ a, V a ∂μ
          = ((ψ 0 - (1 / α₀) * ∫ a, V a ∂μ) / c) * c := by field_simp
        _ ≤ R * c := h2
    have hcoer : ∀ η : ℝ, R ≤ |η| → ψ 0 ≤ ψ η := by
      intro η hη
      by_cases hpos : 0 ≤ η
      · have h1 : R ≤ η := by rwa [abs_of_nonneg hpos] at hη
        have h2 : η ≤ ψ η := by
          have h3 := hG_nonneg η
          simp only [ψ]
          nlinarith [hα₀]
        linarith
      · have hneg : η < 0 := lt_of_not_ge hpos
        have h1 : R ≤ -η := by rw [abs_of_neg hneg] at hη; linarith
        have h2 : (1 / α₀) * (∫ a, V a ∂μ - η) + η ≤ ψ η := by
          have h3 : ∫ a, V a ∂μ - η ≤ G η := hG_ge η
          have h4 : (1 / α₀) * (∫ a, V a ∂μ - η) ≤ (1 / α₀) * G η :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
          simp only [ψ]
          linarith
        have h5 : (1 / α₀) * (∫ a, V a ∂μ - η) + η =
            (1 / α₀) * ∫ a, V a ∂μ - c * η := by
          simp only [hcdef]; ring
        have h6 : c * R ≤ -c * η := by
          have h7 : c * R ≤ c * (-η) := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
          linarith
        linarith
    obtain ⟨η₀, hη₀mem, hη₀min⟩ := isCompact_Icc.exists_isMinOn
      (s := Set.Icc (-R) R) ⟨0, by constructor <;> linarith⟩ hψcont.continuousOn
    have hψmin : ∀ η, ψ η₀ ≤ ψ η := by
      intro η
      by_cases h : |η| ≤ R
      · exact hη₀min ⟨by linarith [neg_abs_le η], by linarith [le_abs_self η]⟩
      · push Not at h
        have h1 : ψ 0 ≤ ψ η := hcoer η h.le
        have h2 : ψ η₀ ≤ ψ 0 := hη₀min ⟨by linarith, by linarith⟩
        linarith
    -- ## subgradient bound 1
    have hpt1 : ∀ (x h : ℝ), 0 < h → max (x - h) 0 - max x 0 = -min (max x 0) h := by
      intro x h hh
      rcases le_total x 0 with hx | hx
      · rw [max_eq_right (by linarith), max_eq_right hx, min_eq_left (by linarith : (0 : ℝ) ≤ h)]; ring
      · rcases le_total x h with hxh | hxh
        · rw [max_eq_right (by linarith), max_eq_left hx, min_eq_left hxh]; ring
        · rw [max_eq_left (by linarith), max_eq_left hx, min_eq_right (by linarith)]; ring
    have hstep1 : ∀ h : ℝ, 0 < h → ∫ a, min (max (V a - η₀) 0) h ∂μ ≤ α₀ * h := by
      intro h hh
      have hdiff : ψ (η₀ + h) - ψ η₀ = h - (1 / α₀) * ∫ a, min (max (V a - η₀) 0) h ∂μ := by
        have hG : G (η₀ + h) - G η₀ = -∫ a, min (max (V a - η₀) 0) h ∂μ := by
          have h1 : G (η₀ + h) - G η₀ =
              ∫ a, (max (V a - (η₀ + h)) 0 - max (V a - η₀) 0) ∂μ := by
            show (∫ a, max (V a - (η₀ + h)) 0 ∂μ) - (∫ a, max (V a - η₀) 0 ∂μ) = _
            rw [integral_sub (hHint (η₀ + h)) (hHint η₀)]
          rw [h1, ← integral_neg]
          congr 1
          funext a
          rw [show V a - (η₀ + h) = (V a - η₀) - h from by ring]
          exact hpt1 (V a - η₀) h hh
        rw [show (1 / α₀) * G (η₀ + h) + (η₀ + h) - ((1 / α₀) * G η₀ + η₀) =
          (1 / α₀) * (G (η₀ + h) - G η₀) + h from by ring, hG]
        ring
      have h2 : 0 ≤ ψ (η₀ + h) - ψ η₀ := by linarith [hψmin (η₀ + h)]
      rw [hdiff] at h2
      have h3 : (1 / α₀) * ∫ a, min (max (V a - η₀) 0) h ∂μ ≤ h := by linarith
      have h4 : α₀ * ((1 / α₀) * ∫ a, min (max (V a - η₀) 0) h ∂μ) ≤ α₀ * h :=
        mul_le_mul_of_nonneg_left h3 hα₀.le
      have he : α₀ * ((1 / α₀) * ∫ a, min (max (V a - η₀) 0) h ∂μ) =
          ∫ a, min (max (V a - η₀) 0) h ∂μ := by field_simp
      linarith
    have hA_le : ∀ h : ℝ, 0 < h → μ.real {a | η₀ + h ≤ V a} ≤ α₀ := by
      intro h hh
      have h1 := hstep1 h hh
      have hmeas : MeasurableSet {a : Ω | η₀ + h ≤ V a} := measurableSet_le measurable_const hVmeas
      have hint_min : Integrable (fun a => min (max (V a - η₀) 0) h) μ := by
        refine Integrable.mono' (hHint η₀) ?_ ?_
        · have h1 : AEStronglyMeasurable (fun a : Ω => max (V a - η₀) 0) μ :=
            (hHint η₀).aestronglyMeasurable
          exact h1.inf aestronglyMeasurable_const
        · filter_upwards with a
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) hh.le)]
          exact min_le_left _ _
      have h2 : h * μ.real {a : Ω | η₀ + h ≤ V a} ≤ ∫ a, min (max (V a - η₀) 0) h ∂μ := by
        have h3 : h * μ.real {a : Ω | η₀ + h ≤ V a} =
            ∫ a, h * ({a : Ω | η₀ + h ≤ V a}.indicator (fun _ => (1 : ℝ))) a ∂μ := by
          rw [integral_const_mul, integral_indicator hmeas, setIntegral_const]
          simp
        rw [h3]
        apply integral_mono_ae
        · exact ((integrable_const (1 : ℝ)).indicator hmeas).const_mul h
        · exact hint_min
        · filter_upwards with a
          by_cases ha : η₀ + h ≤ V a
          · have hmem : a ∈ {a : Ω | η₀ + h ≤ V a} := ha
            rw [Set.indicator_of_mem hmem, mul_one]
            exact le_min (by linarith [le_max_left (V a - η₀) 0]) le_rfl
          · rw [Set.indicator_of_notMem (show a ∉ {a : Ω | η₀ + h ≤ V a} from ha), mul_zero]
            exact le_min (le_max_right _ _) hh.le
      have h4 : h * μ.real {a : Ω | η₀ + h ≤ V a} ≤ h * α₀ := by
        calc h * μ.real _ ≤ ∫ a, min (max (V a - η₀) 0) h ∂μ := h2
          _ ≤ α₀ * h := h1
          _ = h * α₀ := by ring
      exact le_of_mul_le_mul_left h4 hh
    -- ## P(V > η₀) ≤ α₀
    have hP1 : μ.real {a | η₀ < V a} ≤ α₀ := by
      have hmono : Monotone (fun n : ℕ => {a : Ω | η₀ + 1 / ((n : ℝ) + 1) ≤ V a}) := by
        intro m n hmn a ha
        have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast Nat.succ_le_succ hmn
        simp only [Set.mem_ofPred_eq] at ha ⊢
        linarith
      have hunion : ⋃ n : ℕ, {a : Ω | η₀ + 1 / ((n : ℝ) + 1) ≤ V a} = {a | η₀ < V a} := by
        ext a
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        constructor
        · rintro ⟨n, hn⟩
          have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have h2 : 0 < (1 : ℝ) / ((n : ℝ) + 1) := div_pos one_pos hpos
          linarith
        · intro ha
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : 0 < V a - η₀)
          exact ⟨n, by linarith⟩
      have hlim : ∀ n : ℕ, μ {a : Ω | η₀ + 1 / ((n : ℝ) + 1) ≤ V a} ≤ ENNReal.ofReal α₀ := by
        intro n
        have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        have hb := hA_le _ hpos
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal hb
      have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
      rw [hunion] at ht
      have h2 : μ {a | η₀ < V a} ≤ ENNReal.ofReal α₀ :=
        le_of_tendsto ht (Filter.Eventually.of_forall hlim)
      calc μ.real {a | η₀ < V a} = (μ {a | η₀ < V a}).toReal := measureReal_def μ _
        _ ≤ (ENNReal.ofReal α₀).toReal := ENNReal.toReal_mono (by simp) h2
        _ = α₀ := ENNReal.toReal_ofReal hα₀.le
    -- ## subgradient bound 2
    have hpt2 : ∀ (x h : ℝ), 0 < h → max (x + h) 0 - max x 0 = min (max (x + h) 0) h := by
      intro x h hh
      rcases le_total x (-h) with hx | hx
      · rw [max_eq_right (by linarith), max_eq_right (by linarith), min_eq_left (by linarith)]; ring
      · rcases le_total x 0 with hx0 | hx0
        · rw [max_eq_left (by linarith), max_eq_right hx0, min_eq_left (by linarith)]; ring
        · rw [max_eq_left (by linarith), max_eq_left hx0, min_eq_right (by linarith)]; ring
    have hstep2 : ∀ h : ℝ, 0 < h → h ≤ (1 / α₀) * ∫ a, min (max (V a - η₀ + h) 0) h ∂μ := by
      intro h hh
      have hdiff : ψ (η₀ - h) - ψ η₀ = -h + (1 / α₀) * ∫ a, min (max (V a - η₀ + h) 0) h ∂μ := by
        have hG : G (η₀ - h) - G η₀ = ∫ a, min (max (V a - η₀ + h) 0) h ∂μ := by
          have h1 : G (η₀ - h) - G η₀ =
              ∫ a, (max (V a - (η₀ - h)) 0 - max (V a - η₀) 0) ∂μ := by
            show (∫ a, max (V a - (η₀ - h)) 0 ∂μ) - (∫ a, max (V a - η₀) 0 ∂μ) = _
            rw [integral_sub (hHint (η₀ - h)) (hHint η₀)]
          rw [h1]
          congr 1
          funext a
          rw [show V a - (η₀ - h) = (V a - η₀) + h from by ring]
          exact hpt2 (V a - η₀) h hh
        rw [show (1 / α₀) * G (η₀ - h) + (η₀ - h) - ((1 / α₀) * G η₀ + η₀) =
          (1 / α₀) * (G (η₀ - h) - G η₀) - h from by ring, hG]
        ring
      have h2 : 0 ≤ ψ (η₀ - h) - ψ η₀ := by linarith [hψmin (η₀ - h)]
      rw [hdiff] at h2
      linarith
    have hA_ge : ∀ h : ℝ, 0 < h → α₀ ≤ μ.real {a | η₀ - h < V a} := by
      intro h hh
      have h1 := hstep2 h hh
      have hmeas : MeasurableSet {a : Ω | η₀ - h < V a} := measurableSet_lt measurable_const hVmeas
      have hint_min : Integrable (fun a => min (max (V a - η₀ + h) 0) h) μ := by
        refine Integrable.mono' (hHint (η₀ - h)) ?_ ?_
        · have h1 : AEStronglyMeasurable (fun a : Ω => max (V a - (η₀ - h)) 0) μ :=
            (hHint (η₀ - h)).aestronglyMeasurable
          have h2 : (fun a : Ω => min (max (V a - η₀ + h) 0) h) =
              (fun a : Ω => min (max (V a - (η₀ - h)) 0) h) := by
            funext a; congr 2; ring
          rw [h2]
          exact h1.inf aestronglyMeasurable_const
        · filter_upwards with a
          rw [show V a - (η₀ - h) = V a - η₀ + h from by ring] at *
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) hh.le)]
          exact min_le_left _ _
      have h2 : ∫ a, min (max (V a - η₀ + h) 0) h ∂μ ≤ h * μ.real {a : Ω | η₀ - h < V a} := by
        have h3 : h * μ.real {a : Ω | η₀ - h < V a} =
            ∫ a, h * ({a : Ω | η₀ - h < V a}.indicator (fun _ => (1 : ℝ))) a ∂μ := by
          rw [integral_const_mul, integral_indicator hmeas, setIntegral_const]
          simp
        rw [h3]
        apply integral_mono_ae
        · exact hint_min
        · exact ((integrable_const (1 : ℝ)).indicator hmeas).const_mul h
        · filter_upwards with a
          by_cases ha : η₀ - h < V a
          · have hmem : a ∈ {a : Ω | η₀ - h < V a} := ha
            rw [Set.indicator_of_mem hmem, mul_one]
            exact min_le_right _ _
          · rw [Set.indicator_of_notMem (show a ∉ {a : Ω | η₀ - h < V a} from ha), mul_zero]
            have hz : max (V a - η₀ + h) 0 = 0 := by
              rw [max_eq_right]
              linarith [not_lt.mp ha]
            rw [hz, min_eq_left hh.le]
      have h5 : h ≤ (1 / α₀) * (h * μ.real {a : Ω | η₀ - h < V a}) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
      have h6 : (1 : ℝ) ≤ (1 / α₀) * μ.real {a : Ω | η₀ - h < V a} := by
        have h5' : h * 1 ≤ h * ((1 / α₀) * μ.real {a : Ω | η₀ - h < V a}) := by
          calc h * 1 = h := by ring
            _ ≤ (1 / α₀) * (h * μ.real {a : Ω | η₀ - h < V a}) := h5
            _ = h * ((1 / α₀) * μ.real {a : Ω | η₀ - h < V a}) := by ring
        exact le_of_mul_le_mul_left h5' hh
      have h7 : α₀ * ((1 / α₀) * μ.real {a : Ω | η₀ - h < V a}) = μ.real {a : Ω | η₀ - h < V a} := by
        field_simp
      have h8 := mul_le_mul_of_nonneg_left h6 hα₀.le
      rw [mul_one, h7] at h8
      exact h8
    -- ## α₀ ≤ P(V ≥ η₀)
    have hP2 : α₀ ≤ μ.real {a | η₀ ≤ V a} := by
      have hanti : Antitone (fun n : ℕ => {a : Ω | η₀ - 1 / ((n : ℝ) + 1) < V a}) := by
        intro m n hmn a ha
        have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast Nat.succ_le_succ hmn
        simp only [Set.mem_ofPred_eq] at ha ⊢
        linarith
      have hinter : ⋂ n : ℕ, {a : Ω | η₀ - 1 / ((n : ℝ) + 1) < V a} = {a | η₀ ≤ V a} := by
        ext a
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        constructor
        · intro h
          by_contra hc
          push Not at hc
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : 0 < η₀ - V a)
          have := h n
          linarith
        · intro h n
          have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have h2 : 0 < (1 : ℝ) / ((n : ℝ) + 1) := div_pos one_pos hpos
          linarith
      have hlim : ∀ n : ℕ, ENNReal.ofReal α₀ ≤ μ {a : Ω | η₀ - 1 / ((n : ℝ) + 1) < V a} := by
        intro n
        have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        have hb := hA_ge _ hpos
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal hb
      have ht := tendsto_measure_iInter_atTop
        (s := fun n : ℕ => {a : Ω | η₀ - 1 / ((n : ℝ) + 1) < V a})
        (fun n => (measurableSet_lt measurable_const hVmeas).nullMeasurableSet) hanti
        ⟨0, measure_ne_top μ _⟩
      have h2 : ENNReal.ofReal α₀ ≤ μ (⋂ n : ℕ, {a : Ω | η₀ - 1 / ((n : ℝ) + 1) < V a}) :=
        ge_of_tendsto ht (Filter.Eventually.of_forall hlim)
      rw [hinter] at h2
      calc α₀ = (ENNReal.ofReal α₀).toReal := (ENNReal.toReal_ofReal hα₀.le).symm
        _ ≤ (μ {a | η₀ ≤ V a}).toReal := ENNReal.toReal_mono (measure_ne_top μ _) h2
        _ = μ.real {a | η₀ ≤ V a} := (measureReal_def μ _).symm
    -- ## the witness
    set A : Set Ω := {a | η₀ < V a} with hAdef
    set B : Set Ω := {a | V a = η₀} with hBdef
    have hAmeas : MeasurableSet A := measurableSet_lt measurable_const hVmeas
    have hBmeas : MeasurableSet B := hVmeas (measurableSet_singleton η₀)
    have hAB_disj : Disjoint A B := by
      rw [Set.disjoint_left]
      intro a ha hb
      simp only [hAdef, hBdef, Set.mem_setOf_eq] at ha hb
      linarith
    have hAUB : A ∪ B = {a | η₀ ≤ V a} := by
      ext a
      simp only [hAdef, hBdef, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        rcases lt_or_eq_of_le h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'.symm
    have hPAB : α₀ ≤ μ.real A + μ.real B := by
      rw [← measureReal_union hAB_disj hBmeas (measure_ne_top μ _) (measure_ne_top μ _), hAUB]
      exact hP2
    have hPA : μ.real A ≤ α₀ := hP1
    set c₂ : ℝ := (1 - μ.real A / α₀) / μ.real B with hc₂def
    have hc₂_nonneg : 0 ≤ c₂ := by
      rw [hc₂def]
      apply div_nonneg
      · have : μ.real A / α₀ ≤ 1 := by rw [div_le_one hα₀]; exact hPA
        linarith
      · exact measureReal_nonneg
    have hc₂_mul : c₂ * μ.real B = 1 - μ.real A / α₀ := by
      by_cases hB0 : μ.real B = 0
      · rw [hB0, mul_zero]
        have h1 : μ.real A = α₀ := by linarith
        rw [h1, div_self hα₀.ne']
        ring
      · rw [hc₂def, div_mul_cancel₀ _ hB0]
    have hc₂_le : c₂ ≤ 1 / α₀ := by
      by_cases hB0 : μ.real B = 0
      · rw [hc₂def, hB0, div_zero]
        positivity
      · have hBpos : 0 < μ.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm hB0)
        rw [hc₂def, div_le_iff₀ hBpos]
        have h2 : α₀ * (1 - μ.real A / α₀) ≤ α₀ * ((1 / α₀) * μ.real B) := by
          have e1 : α₀ * (1 - μ.real A / α₀) = α₀ - μ.real A := by field_simp
          have e2 : α₀ * ((1 / α₀) * μ.real B) = μ.real B := by field_simp
          rw [e1, e2]
          linarith
        exact le_of_mul_le_mul_left h2 hα₀
    let 𝓛₀ : Ω → ℝ := fun a => if η₀ < V a then 1 / α₀ else if V a = η₀ then c₂ else 0
    have h𝓛₀_meas : Measurable 𝓛₀ := by
      apply Measurable.ite hAmeas measurable_const
      apply Measurable.ite hBmeas measurable_const measurable_const
    have h𝓛₀_nonneg : ∀ a, 0 ≤ 𝓛₀ a := by
      intro a
      simp only [𝓛₀]
      split_ifs with h1 h2
      · positivity
      · exact hc₂_nonneg
      · exact le_rfl
    have h𝓛₀_le : ∀ a, 𝓛₀ a ≤ 1 / α₀ := by
      intro a
      simp only [𝓛₀]
      split_ifs with h1 h2
      · exact le_rfl
      · exact hc₂_le
      · positivity
    have h𝓛₀_eq : 𝓛₀ = (fun a => (A.indicator (fun _ => (1 / α₀))) a + (B.indicator (fun _ => c₂)) a) := by
      funext a
      simp only [𝓛₀, Pi.add_apply]
      by_cases ha : a ∈ A
      · have ha' : η₀ < V a := ha
        have hb : a ∉ B := by
          simp only [hBdef, Set.mem_ofPred_eq]
          linarith
        rw [if_pos ha', Set.indicator_of_mem ha, Set.indicator_of_notMem hb]
        ring
      · have ha' : ¬ (η₀ < V a) := ha
        rw [if_neg ha', Set.indicator_of_notMem ha]
        by_cases hb : a ∈ B
        · have hb' : V a = η₀ := hb
          rw [if_pos hb', Set.indicator_of_mem hb]
          ring
        · have hb' : V a ≠ η₀ := hb
          rw [if_neg hb', Set.indicator_of_notMem hb]
          ring
    have h𝓛₀_int : ∫ a, 𝓛₀ a ∂μ = 1 := by
      rw [h𝓛₀_eq, integral_add]
      · rw [integral_indicator hAmeas, integral_indicator hBmeas, setIntegral_const, setIntegral_const]
        simp only [smul_eq_mul]
        have := hc₂_mul
        field_simp at this ⊢
        linarith
      · exact (integrable_const _).indicator hAmeas
      · exact (integrable_const _).indicator hBmeas
    have hG_eq : G η₀ = ∫ a in A, (V a - η₀) ∂μ := by
      show ∫ a, max (V a - η₀) 0 ∂μ = _
      have h1 : (fun a => max (V a - η₀) 0) = A.indicator (fun a => (V a - η₀)) := by
        funext a
        by_cases ha : a ∈ A
        · rw [Set.indicator_of_mem ha, max_eq_left (by linarith [show η₀ < V a from ha])]
        · rw [Set.indicator_of_notMem ha, max_eq_right (by linarith [show ¬ (η₀ < V a) from ha])]
      rw [h1, integral_indicator hAmeas]
    have hIA : ∫ a in A, (V a - η₀) ∂μ = (∫ a in A, V a ∂μ) - η₀ * μ.real A := by
      rw [integral_sub hVint.integrableOn (integrable_const η₀)]
      rw [setIntegral_const, smul_eq_mul]
      ring
    have h𝓛₀_V : ∫ a, 𝓛₀ a * V a ∂μ = ψ η₀ := by
      have h1 : (fun a => 𝓛₀ a * V a) = (fun a => (1 / α₀) * (A.indicator (fun a => V a)) a + c₂ * (B.indicator (fun a => V a)) a) := by
        funext a
        simp only [𝓛₀, Pi.add_apply]
        by_cases ha : a ∈ A
        · have ha' : η₀ < V a := ha
          have hb : a ∉ B := by
            simp only [hBdef, Set.mem_ofPred_eq]
            linarith
          rw [if_pos ha', Set.indicator_of_mem ha, Set.indicator_of_notMem hb]
          ring
        · have ha' : ¬ (η₀ < V a) := ha
          rw [if_neg ha', Set.indicator_of_notMem ha]
          by_cases hb : a ∈ B
          · have hb' : V a = η₀ := hb
            rw [if_pos hb', Set.indicator_of_mem hb]
            ring
          · have hb' : V a ≠ η₀ := hb
            rw [if_neg hb', Set.indicator_of_notMem hb]
            ring
      rw [h1, integral_add]
      · rw [integral_const_mul, integral_const_mul, integral_indicator hAmeas, integral_indicator hBmeas]
        have hBconst : ∫ a in B, V a ∂μ = η₀ * μ.real B := by
          rw [show ∫ a in B, V a ∂μ = ∫ a in B, η₀ ∂μ from by
            apply setIntegral_congr_fun hBmeas
            intro a ha
            simp only [hBdef, Set.mem_ofPred_eq] at ha
            exact ha]
          rw [setIntegral_const, smul_eq_mul]
          ring
        rw [hBconst]
        have hstep : c₂ * (η₀ * μ.real B) = η₀ * (1 - μ.real A / α₀) := by
          rw [← hc₂_mul]; ring
        rw [hstep]
        simp only [ψ]
        rw [hG_eq, hIA]
        field_simp
        ring
      · exact (hVint.indicator hAmeas).const_mul _
      · exact (hVint.indicator hBmeas).const_mul _
    -- ## IsLUB and IsGLB
    refine ⟨ψ η₀, ?_, ?_⟩
    · constructor
      · intro s hs
        obtain ⟨𝓛, h𝓛meas, h𝓛b, h𝓛int, rfl⟩ := hs
        have h𝓛intble : Integrable 𝓛 μ := by
          refine Integrable.of_bound h𝓛meas.aestronglyMeasurable (1 / α₀) ?_
          filter_upwards with a
          rw [Real.norm_eq_abs, abs_of_nonneg (h𝓛b a).1]
          exact (h𝓛b a).2
        have hint1 : Integrable (fun a => 𝓛 a * (V a - η₀)) μ := by
          have hg : Integrable (fun a => (1 / α₀) * |V a - η₀|) μ :=
            (hVint.sub (integrable_const η₀)).abs.const_mul (1 / α₀)
          have hf : AEStronglyMeasurable (fun a => 𝓛 a * (V a - η₀)) μ :=
            h𝓛meas.aestronglyMeasurable.mul
              (hVmeas.aestronglyMeasurable.sub aestronglyMeasurable_const)
          refine Integrable.mono' hg hf ?_
          filter_upwards with a
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h𝓛b a).1]
          exact mul_le_mul_of_nonneg_right (h𝓛b a).2 (abs_nonneg _)
        have hcomp : ∫ a, 𝓛 a * V a ∂μ =
            ∫ a, 𝓛 a * (V a - η₀) ∂μ + η₀ * ∫ a, 𝓛 a ∂μ := by
          have e : ∀ a, 𝓛 a * V a = 𝓛 a * (V a - η₀) + η₀ * 𝓛 a := by intro a; ring
          rw [funext e, integral_add hint1 (h𝓛intble.const_mul η₀)]
          rw [integral_const_mul (η₀) (fun a => 𝓛 a)]
        rw [hcomp, h𝓛int, mul_one]
        have hle : ∫ a, 𝓛 a * (V a - η₀) ∂μ ≤ (1 / α₀) * ∫ a, max (V a - η₀) 0 ∂μ := by
          have hpt : ∀ a, 𝓛 a * (V a - η₀) ≤ (1 / α₀) * max (V a - η₀) 0 := by
            intro a
            by_cases ha : η₀ < V a
            · rw [max_eq_left (by linarith)]
              exact mul_le_mul_of_nonneg_right (h𝓛b a).2 (by linarith)
            · rw [max_eq_right (by linarith)]
              have hneg : V a - η₀ ≤ 0 := by linarith
              have h0 : 𝓛 a * (V a - η₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (h𝓛b a).1 hneg
              simpa using h0
          calc ∫ a, 𝓛 a * (V a - η₀) ∂μ ≤ ∫ a, (1 / α₀) * max (V a - η₀) 0 ∂μ :=
                integral_mono_ae hint1 ((hHint η₀).const_mul _) (Filter.Eventually.of_forall hpt)
            _ = (1 / α₀) * ∫ a, max (V a - η₀) 0 ∂μ := by
                rw [integral_const_mul]
        have hfin : ψ η₀ = (1 / α₀) * ∫ a, max (V a - η₀) 0 ∂μ + η₀ := rfl
        linarith
      · intro b hb
        exact hb ⟨𝓛₀, h𝓛₀_meas, fun a => ⟨h𝓛₀_nonneg a, h𝓛₀_le a⟩, h𝓛₀_int, h𝓛₀_V.symm⟩
    · constructor
      · rintro s ⟨η, rfl⟩
        exact hψmin η
      · intro b hb
        exact hb ⟨η₀, rfl⟩
  obtain ⟨v, hv1, hv2⟩ := main W' hW'meas hW'int
  refine ⟨v, ?_, ?_⟩
  · have hset : {s : ℝ | ∃ 𝓛 : Ω → ℝ, Measurable 𝓛 ∧ (∀ a, 0 ≤ 𝓛 a ∧ 𝓛 a ≤ 1 / α₀) ∧
        (∫ a, 𝓛 a ∂μ) = 1 ∧ s = ∫ a, 𝓛 a * W a ∂μ} =
        {s : ℝ | ∃ 𝓛 : Ω → ℝ, Measurable 𝓛 ∧ (∀ a, 0 ≤ 𝓛 a ∧ 𝓛 a ≤ 1 / α₀) ∧
          (∫ a, 𝓛 a ∂μ) = 1 ∧ s = ∫ a, 𝓛 a * W' a ∂μ} := by
      ext s
      constructor
      · rintro ⟨𝓛, hm, hb, h1, rfl⟩
        exact ⟨𝓛, hm, hb, h1, by
          apply integral_congr_ae
          filter_upwards [hW'ae] with a ha
          rw [ha]⟩
      · rintro ⟨𝓛, hm, hb, h1, rfl⟩
        exact ⟨𝓛, hm, hb, h1, by
          apply integral_congr_ae
          filter_upwards [hW'ae] with a ha
          rw [ha]⟩
    rwa [hset]
  · have hset : {s : ℝ | ∃ η : ℝ, s = (1 / α₀) * (∫ a, max (W a - η) 0 ∂μ) + η} =
        {s : ℝ | ∃ η : ℝ, s = (1 / α₀) * (∫ a, max (W' a - η) 0 ∂μ) + η} := by
      ext s
      constructor
      · rintro ⟨η, rfl⟩
        exact ⟨η, by
          have h : ∫ a, max (W a - η) 0 ∂μ = ∫ a, max (W' a - η) 0 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hW'ae] with a ha
            rw [ha]
          rw [h]⟩
      · rintro ⟨η, rfl⟩
        exact ⟨η, by
          have h : ∫ a, max (W a - η) 0 ∂μ = ∫ a, max (W' a - η) 0 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hW'ae] with a ha
            rw [ha]
          rw [h]⟩
    rwa [hset]
