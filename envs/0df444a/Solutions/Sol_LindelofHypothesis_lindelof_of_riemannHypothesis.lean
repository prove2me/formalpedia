-- Prove2me | solution 1 for LindelofHypothesis.lindelof_of_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:20:20.263451+00:00
-- url     : https://prove2.me/submissions/74b73e50-01b3-4c32-95b2-65e647a0faf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Theorems.Thm_LindelofHypothesis_mu_convex
import Theorems.Thm_LindelofHypothesis_mu_zero_eq_half
import Theorems.Thm_LindelofHypothesis_mu_half_convexity_bound
import Theorems.Thm_LindelofHypothesis_lindelof_iff_mu_half_eq_zero
import Theorems.Thm_LindelofHypothesis_mu_nonpos_of_riemannHypothesis

open LindelofHypothesis

theorem solution (hRH : RiemannHypothesis) : RiemannVonMangoldt.LindelofHypothesis := by
  obtain ⟨f, hf, hmu⟩ := mu_convex
  have h0 : f 0 = 1 / 2 := by
    have := mu_zero_eq_half
    rw [hmu 0] at this
    exact_mod_cast this
  have hlow : 0 ≤ f (1 / 2) := by
    have := (mu_half_convexity_bound).1
    rw [hmu (1 / 2)] at this
    exact_mod_cast this
  have hup : f (1 / 2) ≤ 0 := by
    by_contra hneg
    push Not at hneg
    set c : ℝ := f (1 / 2) with hc
    set σ : ℝ := 1 / 2 + c with hσ
    have hσpos : 0 < σ := by positivity
    have hσhalf : 1 / 2 < σ := by linarith
    have hfσ : f σ ≤ 0 := by
      have := mu_nonpos_of_riemannHypothesis hRH σ hσhalf
      rw [hmu σ] at this
      exact_mod_cast this
    have ha : 0 ≤ 1 - 1 / (2 * σ) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have hb : 0 ≤ 1 / (2 * σ) := by positivity
    have key := hf.2 (Set.mem_univ 0) (Set.mem_univ σ) ha hb (by ring)
    have hcomb : (1 - 1 / (2 * σ)) • (0 : ℝ) + (1 / (2 * σ)) • σ = 1 / 2 := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hcomb] at key
    simp only [smul_eq_mul, h0] at key
    have h1 : 1 / (2 * σ) * f σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hfσ
    have h2 : c ≤ (1 - 1 / (2 * σ)) * (1 / 2) := by linarith
    have h3 : (1 - 1 / (2 * σ)) * (1 / 2) = (σ - 1 / 2) / (2 * σ) := by
      field_simp
    rw [h3, le_div_iff₀ (by positivity)] at h2
    have : σ - 1 / 2 = c := by rw [hσ]; ring
    rw [this] at h2
    nlinarith
  have hzero : mu (1 / 2) = 0 := by
    rw [hmu (1 / 2)]
    have : f (1 / 2) = 0 := le_antisymm hup hlow
    rw [this]; rfl
  exact lindelof_iff_mu_half_eq_zero.mpr hzero
