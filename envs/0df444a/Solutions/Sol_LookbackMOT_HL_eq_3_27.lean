-- Prove2me | solution 1 for LookbackMOT.HL.eq_3_27
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:17:24.750733+00:00
-- url     : https://prove2.me/submissions/0dc452d9-33bc-4be9-9bfa-157d7a00eb62

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

theorem solution (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (hμpos : μ (Set.Ici 0) = 1) (m : ℝ) (hm : m < X₀) :
    (⨅ ξ : Set.Iio m, phi μ X₀ ξ m) = 0 ∧ phi μ X₀ 0 m = 0 := by
  have hae : ∀ᵐ y ∂μ, 0 ≤ y := by
    rw [ae_iff]
    have h1 : {a : ℝ | ¬ 0 ≤ a} = (Set.Ici (0:ℝ))ᶜ := by
      ext a; simp
    rw [h1, measure_compl measurableSet_Ici (measure_ne_top _ _), hμpos, measure_univ]
    simp
  have hX0 : 0 ≤ X₀ := by
    rw [← hmean]; exact integral_nonneg_of_ae hae
  have hint : ∀ ξ : ℝ, Integrable (fun y : ℝ => y - ξ) μ := fun ξ =>
    (hμ1.sub (integrable_const ξ))
  have hlin : ∀ ξ : ℝ, ∫ y, (y - ξ) ∂μ = X₀ - ξ := by
    intro ξ
    have := integral_sub hμ1 (integrable_const ξ) (μ := μ)
    simp only [id] at this
    rw [this, hmean]
    simp
  -- for ξ ≤ 0, c(ξ) = X₀ - ξ
  have hcneg : ∀ ξ : ℝ, ξ ≤ 0 → callPrice μ ξ = X₀ - ξ := by
    intro ξ hξ
    unfold callPrice
    rw [← hlin ξ]
    apply integral_congr_ae
    filter_upwards [hae] with y hy
    exact max_eq_left (by linarith)
  have hcge : ∀ ξ : ℝ, max (X₀ - ξ) 0 ≤ callPrice μ ξ := by
    intro ξ
    unfold callPrice
    apply max_le
    · rw [← hlin ξ]
      exact integral_mono (hint ξ) (hint ξ).pos_part (fun y => le_max_left _ _)
    · exact integral_nonneg (fun y => le_max_right _ _)
  have hind : (if m < X₀ then (1:ℝ) else 0) = 1 := if_pos hm
  refine ⟨?_, ?_⟩
  · have hnn : ∀ ξ : Set.Iio m, 0 ≤ phi μ X₀ ξ m := by
      rintro ⟨ξ, hξ⟩
      unfold phi c0
      rw [hind, mul_one]
      apply div_nonneg
      · linarith [hcge ξ]
      · have : ξ < m := hξ
        linarith
    apply le_antisymm
    · set ξ₀ : ℝ := min m 0 - 1
      have hξ₀ : ξ₀ ∈ Set.Iio m := by
        simp only [Set.mem_Iio, ξ₀]; linarith [min_le_left m 0]
      have hle0 : ξ₀ ≤ 0 := by simp only [ξ₀]; linarith [min_le_right m 0]
      have hval : phi μ X₀ ξ₀ m = 0 := by
        unfold phi c0
        rw [hind, mul_one, hcneg ξ₀ hle0, max_eq_left (by linarith)]
        simp
      calc (⨅ ξ : Set.Iio m, phi μ X₀ ξ m) ≤ phi μ X₀ (⟨ξ₀, hξ₀⟩ : Set.Iio m) m :=
            ciInf_le (⟨0, by rintro _ ⟨i, rfl⟩; exact hnn i⟩ : BddBelow (Set.range fun ξ : Set.Iio m => phi μ X₀ ξ m)) ⟨ξ₀, hξ₀⟩
        _ = 0 := hval
    · have : Nonempty (Set.Iio m) := ⟨⟨m - 1, by simp⟩⟩
      exact le_ciInf hnn
  · unfold phi c0
    rw [hind, mul_one, hcneg 0 le_rfl, max_eq_left (by linarith)]
    simp
