-- Prove2me | solution 1 for Multihoming.Thresholds.proposition2_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:31:20.095779+00:00
-- url     : https://prove2.me/submissions/82990b97-e2fa-4c1e-9097-61c282652728

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model
set_option autoImplicit false


open Multihoming.Thresholds

lemma th_D_pos (t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) : 0 < 4 * t ^ 2 - 3 * t * μ + μ ^ 2 := by
  nlinarith [sq_nonneg (2 * t - 3 * μ / 4), sq_nonneg μ]

lemma th_piM (t μ e : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    piM t μ e = t * (t - μ) * (e + μ) ^ 2 / ((t + μ) * (2 * t - μ) ^ 2) := by
  have a1 : t + μ ≠ 0 := by linarith
  have a2 : t - μ ≠ 0 := by linarith
  have a3 : 2 * t - μ ≠ 0 := by linarith
  have a5 : t ≠ 0 := ht.ne'
  have e1 : t * 2 - μ ≠ 0 := by linarith
  have h5 : t ^ 2 - μ ^ 2 = (t - μ) * (t + μ) := by ring
  have hD : demandM t μ e (pM t μ e) (pM t μ e) = t * (μ + e) / ((2 * t - μ) * (t + μ)) := by
    unfold demandM pM
    rw [h5]
    field_simp
    ring
  unfold piM
  rw [hD]
  unfold pM
  field_simp
  ring

lemma th_diff (t μ e : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) :
    piM t μ e - piM t 0 e =
      -(μ * (( 4 * t ^ 2 - 3 * t * μ + μ ^ 2) * e ^ 2 - 8 * t ^ 2 * (t - μ) * e
          - 4 * t ^ 2 * (t - μ) * μ)) / (4 * t * (t + μ) * (2 * t - μ) ^ 2) := by
  have a1 : t + μ ≠ 0 := by linarith
  have a3 : 2 * t - μ ≠ 0 := by linarith
  have a5 : t ≠ 0 := ht.ne'
  have e1 : t * 2 - μ ≠ 0 := by linarith
  rw [th_piM t μ e ht hμ.le hμt, th_piM t 0 e ht le_rfl ht]
  field_simp
  ring

/-- factorisation of the quadratic -/
lemma th_fac (t μ e : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) :
    ((4 * t ^ 2 - 3 * t * μ + μ ^ 2) * e ^ 2 - 8 * t ^ 2 * (t - μ) * e - 4 * t ^ 2 * (t - μ) * μ) =
      (e - ePi t μ) * ((4 * t ^ 2 - 3 * t * μ + μ ^ 2) * e + 2 * t * (2 * t - μ) * Real.sqrt (t ^ 2 - μ ^ 2)
        - 4 * t ^ 2 * (t - μ)) := by
  have hD := th_D_pos t μ ht hμ.le hμt
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (t ^ 2 - μ ^ 2) := ⟨_, rfl⟩
  have hS2 : S ^ 2 = t ^ 2 - μ ^ 2 := by rw [hS]; exact Real.sq_sqrt (by nlinarith)
  rw [← hS]
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = 4 * t ^ 2 - 3 * t * μ + μ ^ 2 := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by rw [hDd]; exact hD.ne'
  have hE : ePi t μ * D = 4 * t ^ 2 * (t - μ) + 2 * t * (2 * t - μ) * S := by
    unfold ePi
    rw [← hS, ← hDd]
    field_simp
  have hY : (2 * t * (2 * t - μ) * S) ^ 2 - (4 * t ^ 2 * (t - μ)) ^ 2 = 4 * t ^ 2 * (t - μ) * μ * D := by
    rw [hDd]
    linear_combination (4 * t ^ 2 * (2 * t - μ) ^ 2) * hS2
  have hKey : ePi t μ * (2 * t * (2 * t - μ) * S - 4 * t ^ 2 * (t - μ)) = 4 * t ^ 2 * (t - μ) * μ := by
    have h0 : D * (ePi t μ * (2 * t * (2 * t - μ) * S - 4 * t ^ 2 * (t - μ)) - 4 * t ^ 2 * (t - μ) * μ) = 0 := by
      linear_combination (2 * t * (2 * t - μ) * S - 4 * t ^ 2 * (t - μ)) * hE + hY
    have := (mul_eq_zero.mp h0).resolve_left hD0
    linarith
  rw [← hDd]
  linear_combination e * hE + hKey

lemma th_pt (t μ e : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) (he : 0 ≤ e) :
    (e < ePi t μ → piM t 0 e < piM t μ e) ∧
    (ePi t μ < e → piM t μ e < piM t 0 e) := by
  have hD := th_D_pos t μ ht hμ.le hμt
  have hfac := th_fac t μ e ht hμ hμt
  have hdiff := th_diff t μ e ht hμ hμt
  rw [hfac] at hdiff
  have hS : 0 < Real.sqrt (t ^ 2 - μ ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hS2 : Real.sqrt (t ^ 2 - μ ^ 2) ^ 2 = t ^ 2 - μ ^ 2 := Real.sq_sqrt (by nlinarith)
  -- X < Y
  have hXY : 4 * t ^ 2 * (t - μ) < 2 * t * (2 * t - μ) * Real.sqrt (t ^ 2 - μ ^ 2) := by
    have hY0 : 0 < 2 * t * (2 * t - μ) * Real.sqrt (t ^ 2 - μ ^ 2) := by
      have : 0 < 2 * t - μ := by linarith
      positivity
    have hsq : (4 * t ^ 2 * (t - μ)) ^ 2 < (2 * t * (2 * t - μ) * Real.sqrt (t ^ 2 - μ ^ 2)) ^ 2 := by
      have e1 : (2 * t * (2 * t - μ) * Real.sqrt (t ^ 2 - μ ^ 2)) ^ 2 - (4 * t ^ 2 * (t - μ)) ^ 2 =
          4 * t ^ 2 * (t - μ) * μ * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) := by
        linear_combination (4 * t ^ 2 * (2 * t - μ) ^ 2) * hS2
      have : 0 < 4 * t ^ 2 * (t - μ) * μ * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) := by
        have : 0 < t - μ := by linarith
        positivity
      linarith
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have := pow_le_pow_left₀ hY0.le hcon 2
    linarith
  have hpos : 0 < (4 * t ^ 2 - 3 * t * μ + μ ^ 2) * e + 2 * t * (2 * t - μ) * Real.sqrt (t ^ 2 - μ ^ 2)
        - 4 * t ^ 2 * (t - μ) := by
    have : 0 ≤ (4 * t ^ 2 - 3 * t * μ + μ ^ 2) * e := mul_nonneg hD.le he
    linarith
  have hden : 0 < 4 * t * (t + μ) * (2 * t - μ) ^ 2 := by
    have : 0 < 2 * t - μ := by linarith
    positivity
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = (4 * t ^ 2 - 3 * t * μ + μ ^ 2) * e +
      2 * t * (2 * t - μ) * Real.sqrt (t ^ 2 - μ ^ 2) - 4 * t ^ 2 * (t - μ) := ⟨_, rfl⟩
  rw [← hF] at hdiff hpos
  constructor
  · intro h
    have : 0 < piM t μ e - piM t 0 e := by
      rw [hdiff]
      apply div_pos _ hden
      have : (e - ePi t μ) * F < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
      nlinarith
    linarith
  · intro h
    have : piM t μ e - piM t 0 e < 0 := by
      rw [hdiff]
      apply div_neg_of_neg_of_pos _ hden
      have : 0 < (e - ePi t μ) * F := mul_pos (by linarith) hpos
      nlinarith
    linarith

theorem solution (t μ e : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t)
    (hlo : eLow t μ ≤ e) (hhi : e ≤ eBar t μ) :
    (e < eP t μ → pM t 0 e < pM t μ e) ∧ (eP t μ < e → pM t μ e < pM t 0 e) ∧
    (e < ePi t μ → piM t 0 e < piM t μ e) ∧ (ePi t μ < e → piM t μ e < piM t 0 e) ∧
    eP t μ < ePi t μ := by
  have htm : 0 < t - μ := by linarith
  have he : 0 ≤ e := by
    have : 0 < eLow t μ := by
      unfold eLow
      have : 0 < 2 * t + μ := by linarith
      positivity
    linarith
  have a3 : 2 * t - μ ≠ 0 := by linarith
  have a5 : t ≠ 0 := ht.ne'
  have e1 : t * 2 - μ ≠ 0 := by linarith
  have hpM : pM t μ e - pM t 0 e = μ * (2 * (t - μ) - e) / (2 * (2 * t - μ)) := by
    unfold pM
    field_simp
    ring
  have hden : 0 < 2 * (2 * t - μ) := by linarith
  have hD := th_D_pos t μ ht hμ.le hμt
  have hS : 0 < Real.sqrt (t ^ 2 - μ ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hS2 : Real.sqrt (t ^ 2 - μ ^ 2) ^ 2 = t ^ 2 - μ ^ 2 := Real.sq_sqrt (by nlinarith)
  refine ⟨?_, ?_, (th_pt t μ e ht hμ hμt he).1, (th_pt t μ e ht hμ hμt he).2, ?_⟩
  · intro h
    unfold eP at h
    have : 0 < pM t μ e - pM t 0 e := by
      rw [hpM]
      exact div_pos (mul_pos hμ (by linarith)) hden
    linarith
  · intro h
    unfold eP at h
    have : pM t μ e - pM t 0 e < 0 := by
      rw [hpM]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hμ (by linarith)) hden
    linarith
  · have hs : (t - μ) ^ 2 < t * Real.sqrt (t ^ 2 - μ ^ 2) := by
      by_contra hcon
      replace hcon := not_lt.mp hcon
      have h0 : 0 ≤ t * Real.sqrt (t ^ 2 - μ ^ 2) := by positivity
      have h1 := pow_le_pow_left₀ h0 hcon 2
      have h2 : (t * Real.sqrt (t ^ 2 - μ ^ 2)) ^ 2 = t ^ 2 * (t ^ 2 - μ ^ 2) := by
        rw [mul_pow, hS2]
      have h3 : 0 < (t - μ) * μ * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) := by positivity
      nlinarith
    unfold eP ePi
    rw [lt_div_iff₀ hD]
    have := mul_lt_mul_of_pos_left hs hden
    nlinarith
