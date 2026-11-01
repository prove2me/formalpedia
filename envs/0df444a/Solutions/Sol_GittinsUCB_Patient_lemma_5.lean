-- Prove2me | solution 1 for GittinsUCB.Patient.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:28:10.375068+00:00
-- url     : https://prove2.me/submissions/af98e324-e22d-416a-9d7d-81ff8d44145b

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
import Theorems.Thm_GittinsUCB_Patient_equation_5
import Theorems.Thm_GittinsUCB_Patient_lemma_4
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ γ : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
        gittinsIndex σW2 γ 0 1 ≤
          Real.sqrt (2 * Real.log (1 / (1 - γ))) + ε := by
  intro ε hε
  -- eventually `0 < γ < 1` and `1/(1-γ) ≥ e²`
  have hev : ∀ᶠ γ : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      γ ∈ Set.Ioo (1 - Real.exp (-2)) 1 := by
    have h : 1 - Real.exp (-2) < 1 := by have := Real.exp_pos (-2); linarith
    exact Ioo_mem_nhdsLT h
  filter_upwards [hev] with γ hγ
  obtain ⟨hγl, hγ1⟩ := hγ
  have hγ0 : 0 < γ := by
    have : Real.exp (-2) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have := Real.add_one_le_exp (2:ℝ); linarith
    linarith
  have h1γ : 0 < 1 - γ := by linarith
  set u := Real.log (1 / (1 - γ)) with hu
  have hu2 : 2 ≤ u := by
    rw [hu, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ h1γ]
    have : 1 - γ < Real.exp (-2) := by linarith
    have h22 : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos 2]
  set a := Real.sqrt (2 * u) with ha
  have ha2 : 2 ≤ a := by
    rw [ha, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  -- every admissible tax is at most `a`
  have hbound : ∀ lam ∈ {lam : ℝ | 0 ≤ value σW2 γ lam 0 1}, lam ≤ a := by
    intro lam hlam
    simp only [Set.mem_setOf_eq] at hlam
    by_contra hlt
    rw [not_le] at hlt
    have hlam2 : 2 ≤ lam := by linarith
    have h5 := equation_5 σW2 hW γ lam hγ0 hγ1
    have hint : (∫ ω, max (θ ω - lam) 0 ∂(model 0 1 σW2)) =
        ∫ x : ℝ, max (x - lam) 0 ∂(gaussianReal 0 1) := by
      unfold model θ
      exact (integral_fun_fst (μ := gaussianReal 0 1) (fun x : ℝ => max (x - lam) 0)).trans
        (by simp)
    have h4 := (lemma_4 1 lam one_pos (by linarith)).2
    have e : (gaussianReal 0 ⟨(1:ℝ) ^ 2, sq_nonneg 1⟩ : Measure ℝ) = gaussianReal 0 1 := by
      congr 1; exact NNReal.eq (show ((1:ℝ)^2) = 1 by norm_num)
    rw [e, ← hint, div_one, one_mul] at h4
    have hc : 0 ≤ γ / (1 - γ) := by positivity
    have key : lam ≤ γ / (1 - γ) * stdPdf lam := by
      have := mul_le_mul_of_nonneg_left h4 hc
      linarith
    unfold stdPdf at key
    set E := Real.exp (-lam ^ 2 / 2) with hE
    have hpi : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have := Real.pi_gt_three; linarith
    have hsq0 : 0 < Real.sqrt (2 * Real.pi) := by linarith
    -- (1-γ)/γ ≤ exp(-lam²/2)
    have k2 : (1 - γ) ≤ γ * E := by
      have : lam * (1 - γ) * Real.sqrt (2 * Real.pi) ≤ γ * E := by
        rw [div_mul_div_comm, le_div_iff₀ (by positivity)] at key
        nlinarith
      have : 1 - γ ≤ lam * (1 - γ) * Real.sqrt (2 * Real.pi) := by
        have h1 : 1 ≤ lam * Real.sqrt (2 * Real.pi) := by nlinarith
        nlinarith
      linarith
    have k3 : 1 - γ ≤ E := by
      have : γ * E ≤ E := by
        have := Real.exp_pos (-lam ^ 2 / 2)
        nlinarith
      linarith
    have k4 : Real.log (1 - γ) ≤ -lam ^ 2 / 2 := by
      rw [hE] at k3
      have := Real.log_le_log h1γ k3
      rwa [Real.log_exp] at this
    have k5 : lam ^ 2 ≤ 2 * u := by
      rw [hu, one_div, Real.log_inv]; linarith
    have : lam ≤ a := by
      rw [ha]; exact Real.le_sqrt_of_sq_le k5
    linarith
  have hS : gittinsIndex σW2 γ 0 1 ≤ a := by
    unfold gittinsIndex
    rcases Set.eq_empty_or_nonempty {lam : ℝ | 0 ≤ value σW2 γ lam 0 1} with h | h
    · rw [h, Real.sSup_empty]; linarith
    · exact csSup_le h hbound
  linarith
