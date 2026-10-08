-- Prove2me | solution 1 for LocalRademacher.StarHull.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:55:59.214666+00:00
-- url     : https://prove2.me/submissions/4591d434-ac1f-4470-bd72-c9fe9a7d0276

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

set_option autoImplicit false

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized LocalRademacher.StarHull in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X) {n : ℕ} (s : Fin n → X)
    (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (B K r : ℝ) (hB : 0 < B) (hK : 1 < K) (hr : 0 < r)
    (hT0 : ∀ f ∈ F, 0 ≤ T f) (hTB : ∀ f ∈ F, T f ≤ B * ∫ y, f y ∂P) :
    ((∀ g ∈ tildeG F T r, (∫ y, g y ∂P) - empMean s g ≤ r / (B * K)) →
        ∀ f ∈ F, ∫ y, f y ∂P ≤ max (empMean s f) (K / (K - 1) * empMean s f) + r / (B * K)) ∧
      ((∀ g ∈ tildeG F T r, empMean s g - ∫ y, g y ∂P ≤ r / (B * K)) →
        ∀ f ∈ F, empMean s f ≤ (K + 1) / K * ∫ y, f y ∂P + r / (B * K)) := by
  have hK0 : 0 < K := by linarith
  have hBK : 0 < B * K := mul_pos hB hK0
  have he : 0 < r / (B * K) := div_pos hr hBK
  -- linearity facts for the rescaled function
  have hint : ∀ (c : ℝ) (f : X → ℝ), ∫ y, (fun x => c * f x) y ∂P = c * ∫ y, f y ∂P := by
    intro c f
    exact integral_const_mul c f
  have hemp : ∀ (c : ℝ) (f : X → ℝ), empMean s (fun x => c * f x) = c * empMean s f := by
    intro c f
    unfold empMean
    rw [← Finset.mul_sum]
    ring
  have hmem : ∀ f ∈ F, (fun x => (r / max (T f) r) * f x) ∈ tildeG F T r :=
    fun f hf => ⟨f, hf, rfl⟩
  -- key cancellation in the case T f > r
  have key : ∀ f ∈ F, ∀ D : ℝ, r < T f → r / T f * D ≤ r / (B * K) →
      K * D ≤ ∫ y, f y ∂P := by
    intro f hf D hTr h
    have hT : 0 < T f := lt_trans hr hTr
    have h1 : r * D / T f ≤ r / (B * K) := by
      rw [div_mul_eq_mul_div] at h; exact h
    rw [div_le_div_iff₀ hT hBK] at h1
    have h2 : D * (B * K) ≤ T f := by
      have : r * (D * (B * K)) ≤ r * T f := by nlinarith
      exact le_of_mul_le_mul_left this hr
    have h3 := hTB f hf
    have h4 : B * (K * D) ≤ B * ∫ y, f y ∂P := by nlinarith
    exact le_of_mul_le_mul_left h4 hB
  refine ⟨?_, ?_⟩
  · intro hV f hf
    have h := hV _ (hmem f hf)
    rw [hint, hemp, ← mul_sub] at h
    set Pf := ∫ y, f y ∂P
    set Pn := empMean s f
    rcases le_or_gt (T f) r with hTr | hTr
    · rw [max_eq_right hTr, div_self (ne_of_gt hr), one_mul] at h
      have : Pn ≤ max Pn (K / (K - 1) * Pn) := le_max_left _ _
      linarith
    · rw [max_eq_left hTr.le] at h
      have hk := key f hf (Pf - Pn) hTr h
      have hK1 : 0 < K - 1 := by linarith
      have hle : Pf ≤ K / (K - 1) * Pn := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hK1]
        nlinarith
      have : K / (K - 1) * Pn ≤ max Pn (K / (K - 1) * Pn) := le_max_right _ _
      linarith
  · intro hV f hf
    have h := hV _ (hmem f hf)
    rw [hint, hemp, ← mul_sub] at h
    have hPf : 0 ≤ ∫ y, f y ∂P := by
      have h0 := hT0 f hf
      have h3 := hTB f hf
      have : 0 ≤ B * ∫ y, f y ∂P := le_trans h0 h3
      exact nonneg_of_mul_nonneg_right (by linarith) hB
    set Pf := ∫ y, f y ∂P
    set Pn := empMean s f
    have hgoal : (K + 1) / K * Pf = Pf + Pf / K := by
      field_simp
    rcases le_or_gt (T f) r with hTr | hTr
    · rw [max_eq_right hTr, div_self (ne_of_gt hr), one_mul] at h
      have : 0 ≤ Pf / K := div_nonneg hPf hK0.le
      rw [hgoal]
      linarith
    · rw [max_eq_left hTr.le] at h
      have hk := key f hf (Pn - Pf) hTr h
      have hle : Pn ≤ (K + 1) / K * Pf := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hK0]
        nlinarith
      linarith
