-- Prove2me | solution 1 for LookbackMOT.HL.lemma_3_3_step_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:19:07.184658+00:00
-- url     : https://prove2.me/submissions/ed392243-3247-4af0-967c-cdba81340979

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

theorem solution (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    g X₀ + ∫ y in Set.Ici X₀, (ν (Set.Ici y)).toReal * deriv g y = ∫ x, g x ∂ν := by
  obtain ⟨hνprob, hνI⟩ := hν
  -- call price facts
  have hint : ∀ ξ : ℝ, Integrable (fun y : ℝ => y - ξ) μ := fun ξ =>
    (hμ1.sub (integrable_const ξ))
  have hlin : ∀ ξ : ℝ, ∫ y, (y - ξ) ∂μ = X₀ - ξ := by
    intro ξ
    have := integral_sub hμ1 (integrable_const ξ) (μ := μ)
    simp only [id] at this
    rw [this, hmean]
    simp
  have hputint : ∀ ξ : ℝ, Integrable (fun y : ℝ => max (ξ - y) 0) μ := fun ξ =>
    ((integrable_const ξ).sub hμ1).pos_part
  have hcdec : ∀ ξ : ℝ, callPrice μ ξ = (X₀ - ξ) + ∫ y, max (ξ - y) 0 ∂μ := by
    intro ξ
    unfold callPrice
    rw [← hlin ξ, ← integral_add (hint ξ) (hputint ξ)]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only
    rcases le_total y ξ with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  set Pp : ℝ := ∫ y, max (X₀ - y) 0 ∂μ
  have hPp : 0 ≤ Pp := integral_nonneg (fun y => le_max_right _ _)
  have hput_le : ∀ ξ : ℝ, ξ ≤ X₀ → ∫ y, max (ξ - y) 0 ∂μ ≤ Pp := by
    intro ξ hξ
    exact integral_mono (hputint ξ) (hputint X₀) (fun y => max_le_max (by linarith) le_rfl)
  have hput_nn : ∀ ξ : ℝ, 0 ≤ ∫ y, max (ξ - y) 0 ∂μ := fun ξ =>
    integral_nonneg (fun y => le_max_right _ _)
  -- ν([X₀, ∞)) = 1
  have hinf : (⨅ ξ : Set.Iio X₀, callPrice μ ξ / (X₀ - ξ)) = 1 := by
    have hge : ∀ ξ : Set.Iio X₀, 1 ≤ callPrice μ ξ / (X₀ - ξ) := by
      rintro ⟨ξ, hξ⟩
      have hξ' : ξ < X₀ := hξ
      rw [le_div_iff₀ (by linarith), one_mul, hcdec]
      linarith [hput_nn ξ]
    have hbdd : BddBelow (Set.range fun ξ : Set.Iio X₀ => callPrice μ ξ / (X₀ - ξ)) :=
      ⟨1, by rintro _ ⟨i, rfl⟩; exact hge i⟩
    have : Nonempty (Set.Iio X₀) := ⟨⟨X₀ - 1, by simp⟩⟩
    apply le_antisymm _ (le_ciInf hge)
    apply le_of_forall_pos_lt_add
    intro ε hε
    set ξ : ℝ := X₀ - Pp / ε - 1
    have hξ : ξ ∈ Set.Iio X₀ := by
      simp only [Set.mem_Iio, ξ]; linarith [div_nonneg hPp hε.le]
    have hpos : 0 < X₀ - ξ := by simp only [ξ]; linarith [div_nonneg hPp hε.le]
    calc (⨅ ξ : Set.Iio X₀, callPrice μ ξ / (X₀ - ξ)) ≤ callPrice μ ξ / (X₀ - ξ) :=
          ciInf_le hbdd ⟨ξ, hξ⟩
      _ < 1 + ε := by
          rw [div_lt_iff₀ hpos, hcdec]
          have h1 := hput_le ξ (le_of_lt hξ)
          have h2 : X₀ - ξ = Pp / ε + 1 := by simp only [ξ]; ring
          rw [h2]
          have h3 : ε * (Pp / ε) = Pp := by field_simp
          nlinarith
  have hνX : ν (Set.Ici X₀) = 1 := by rw [hνI, hinf]; simp
  have hνae : ∀ᵐ x ∂ν, X₀ ≤ x := by
    rw [ae_iff]
    have h1 : {a : ℝ | ¬ X₀ ≤ a} = (Set.Ici X₀)ᶜ := by ext a; simp
    rw [h1, measure_compl measurableSet_Ici (measure_ne_top _ _), hνX, measure_univ]
    simp
  -- derivative facts
  set D := deriv g
  have hdiff : Differentiable ℝ g := hgC1.differentiable (by norm_num)
  have hDcont : Continuous D := hgC1.continuous_deriv (by norm_num)
  have hDnn : ∀ x, 0 ≤ D x := fun x => hgmono.deriv_nonneg
  have hFTC : ∀ s : ℝ, ∫ t in (0:ℝ)..s, D (X₀ + t) = g (X₀ + s) - g X₀ := by
    intro s
    rw [intervalIntegral.integral_comp_add_left (fun t => D t) X₀]
    simp only [add_zero]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _; exact (hdiff x).hasDerivAt
    · exact hDcont.intervalIntegrable _ _
  -- layer cake
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul ν (f := fun x => x - X₀)
    (g := fun t => D (X₀ + t))
    (by filter_upwards [hνae] with x hx; simp only [Pi.zero_apply]; linarith)
    (by fun_prop)
    (fun t _ => (hDcont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
    (Filter.Eventually.of_forall (fun t => hDnn _))
  simp only [hFTC, add_sub_cancel] at hlc
  have hset : ∀ t : ℝ, {a : ℝ | t ≤ a - X₀} = Set.Ici (X₀ + t) := by
    intro t; ext a; simp; constructor <;> intro h <;> linarith
  simp only [hset] at hlc
  -- translate the right side
  have htrans : ∫⁻ t in Set.Ioi 0, ν (Set.Ici (X₀ + t)) * ENNReal.ofReal (D (X₀ + t)) =
      ∫⁻ y in Set.Ioi X₀, ν (Set.Ici y) * ENNReal.ofReal (D y) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
    rw [← lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
      (Set.indicator (Set.Ioi X₀) fun y => ν (Set.Ici y) * ENNReal.ofReal (D y)) X₀]
    congr 1
    ext t
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (by simpa using ht), Set.indicator_of_mem (by simpa using ht)]
    · rw [Set.indicator_of_notMem (by simpa using ht), Set.indicator_of_notMem (by simpa using ht)]
  rw [htrans] at hlc
  -- convert to real integrals
  have hL : ∫ x, (g x - g X₀) ∂ν = (∫⁻ x, ENNReal.ofReal (g x - g X₀) ∂ν).toReal := by
    apply integral_eq_lintegral_of_nonneg_ae
    · filter_upwards [hνae] with x hx; simp only [Pi.zero_apply]; linarith [hgmono hx]
    · exact (hνg.sub (integrable_const _)).aestronglyMeasurable
  have hR : ∫ y in Set.Ioi X₀, (ν (Set.Ici y)).toReal * D y =
      (∫⁻ y in Set.Ioi X₀, ν (Set.Ici y) * ENNReal.ofReal (D y)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    · exact Filter.Eventually.of_forall (fun y => mul_nonneg ENNReal.toReal_nonneg (hDnn y))
    · apply Measurable.aestronglyMeasurable
      apply Measurable.mul _ hDcont.measurable
      apply Measurable.ennreal_toReal
      have : Antitone fun y : ℝ => ν (Set.Ici y) := fun a b hab =>
        measure_mono (Set.Ici_subset_Ici.mpr hab)
      exact this.measurable
  rw [integral_Ici_eq_integral_Ioi, hR, ← hlc, ← hL, integral_sub hνg (integrable_const _)]
  simp
