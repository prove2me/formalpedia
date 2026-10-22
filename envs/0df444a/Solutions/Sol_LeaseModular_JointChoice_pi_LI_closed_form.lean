-- Prove2me | solution 1 for LeaseModular.JointChoice.pi_LI_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:02:48.209143+00:00
-- url     : https://prove2.me/submissions/6a1b7ec2-140f-426d-9945-b8399ebc450c

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

open LeaseModular.JointChoice

namespace LMLI

noncomputable def FL (P : Params) (x t s : ℝ) : ℝ :=
  ((1 - P.γ*P.δ₁)/2 - P.c)*x - (1 - P.γ*P.δ₁)/2*x^2 + ((1 - P.γ*P.δ₂)/2 - P.c)*t
    - (1 - P.γ*P.δ₂)/2*t^2 + P.γ*(P.δ₁+P.δ₂)/2*(s - s^2)

lemma profitLI_eq (P : Params) (y : LIQty) :
    profitLI P y = FL P y.n y.n (y.n+y.u) := by
  unfold profitLI rLIn rLIu FL δ₁l δ₂l; ring

end LMLI

open LMLI in
theorem solution (P : Params) (hP : Standing P) :
    (P.c < CLI P.δ₁ P.δ₂ P.γ →
      IsOptLI P (((2 - P.γ * (P.δ₁ + P.δ₂)) * (1 - 4 * P.c) + 8 * P.c ^ 2) /
        (4 * (2 - P.γ * (P.δ₁ + P.δ₂)))) ∧
      ∀ x, IsMaxLI P x → 0 < x.u ∧ x.u < x.n) ∧
    (CLI P.δ₁ P.δ₂ P.γ ≤ P.c →
      IsOptLI P ((2 - 4 * P.c + P.γ * (P.δ₁ + P.δ₂)) ^ 2 /
        (8 * (2 + 3 * P.γ * (P.δ₁ + P.δ₂)))) ∧
      ∀ x, IsMaxLI P x → 0 < x.u ∧ x.u = x.n) := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl⟩ := hP
  simp only at *
  have hgd2 : g*d2 < g*d1 := mul_lt_mul_of_pos_left hd21 hg
  have hgd2p : 0 < g*d2 := mul_pos hg hd2
  have hB : 0 < g*(d1+d2) := mul_pos hg (by linarith)
  have hsp : g*(d1+d2) = g*d1 + g*d2 := by ring
  have hB2 : (0:ℝ) ≤ g*(d1+d2)/2 := by linarith
  simp only [CLI]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hD : 0 < 2 - g*(d1+d2) := by linarith
    set n := ((2 - g*(d1+d2))/2 - 2*c)/(2 - g*(d1+d2)) with hndef
    have hn : (2 - g*(d1+d2))*n = (2 - g*(d1+d2))/2 - 2*c := mul_div_cancel₀ _ hD.ne'
    have hn4 : 1/4 < n := by
      by_contra hh; push Not at hh
      have := mul_le_mul_of_nonneg_left hh hD.le; linarith
    have hn2 : n < 1/2 := by
      by_contra hh; push Not at hh
      have := mul_le_mul_of_nonneg_left hh hD.le; linarith
    have hval : FL ⟨d1,d2,g,c⟩ n n (1/2) =
        ((2 - g * (d1 + d2)) * (1 - 4 * c) + 8 * c ^ 2) / (4 * (2 - g * (d1 + d2))) := by
      unfold FL; simp only; rw [hndef]
      rw [show g*(d1+d2) = (1 - (1-g*d1)) + (1 - (1-g*d2)) by ring]
      have hD' := hD.ne'
      rw [show g*(d1+d2) = (1 - (1-g*d1)) + (1 - (1-g*d2)) by ring] at hD'
      generalize 1 - g*d1 = p at *
      generalize 1 - g*d2 = q at *
      generalize hE : 2 - (1 - p + (1 - q)) = E at *
      field_simp
      subst hE
      ring
    have key : ∀ y1 y3 : ℝ, FL ⟨d1,d2,g,c⟩ n n (1/2) - FL ⟨d1,d2,g,c⟩ y1 y1 y3 =
        (2 - g*(d1+d2))/2 * (y1 - n)^2 + g*(d1+d2)/2 * (y3 - 1/2)^2 := by
      intro y1 y3
      unfold FL; simp only
      linear_combination (y1 - n) * hn
    refine ⟨⟨⟨⟨n, 1/2 - n⟩, ⟨by simp only; linarith, by simp only; linarith⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [profitLI_eq]; simp only; rw [← hval]; congr 1; ring
    · rintro v ⟨y, hy, rfl⟩
      rw [profitLI_eq, ← hval]
      have := key y.n (y.n + y.u)
      have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (2 - g*(d1+d2))/2) (sq_nonneg (y.n - n))
      have a2 := mul_nonneg hB2 (sq_nonneg (y.n + y.u - 1/2))
      linarith
    · intro x ⟨hx, hmax⟩
      have hfe : (⟨n, 1/2 - n⟩ : LIQty) ∈ feasLI := ⟨by simp only; linarith, by simp only; linarith⟩
      have h1 := hmax _ hfe
      rw [profitLI_eq, profitLI_eq] at h1
      simp only at h1
      have e := key x.n (x.n + x.u)
      rw [show n + (1/2 - n) = 1/2 by ring] at h1
      have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (2 - g*(d1+d2))/2) (sq_nonneg (x.n - n))
      have a2 := mul_nonneg hB2 (sq_nonneg (x.n + x.u - 1/2))
      have z1 : (2 - g*(d1+d2))/2 * (x.n - n)^2 = 0 := by linarith
      have z2 : g*(d1+d2)/2 * (x.n + x.u - 1/2)^2 = 0 := by linarith
      have e1 : x.n = n := by
        rcases mul_eq_zero.mp z1 with h3 | h3
        · linarith
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3; linarith
      have e2 : x.n + x.u = 1/2 := by
        rcases mul_eq_zero.mp z2 with h3 | h3
        · linarith
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3; linarith
      constructor <;> linarith
  · have hD : 0 < 2 + 3*(g*(d1+d2)) := by linarith
    set n := (1 + g*(d1+d2)/2 - 2*c)/(2 + 3*(g*(d1+d2))) with hndef
    have hn : (2 + 3*(g*(d1+d2)))*n = 1 + g*(d1+d2)/2 - 2*c := mul_div_cancel₀ _ hD.ne'
    have hn0 : 0 < n := by
      by_contra hh; push Not at hh
      have := mul_nonpos_of_nonneg_of_nonpos hD.le hh; linarith
    have hn4 : n ≤ 1/4 := by
      by_contra hh; push Not at hh
      have := mul_lt_mul_of_pos_left hh hD; linarith
    have hval : FL ⟨d1,d2,g,c⟩ n n (2*n) =
        (2 - 4 * c + g * (d1 + d2)) ^ 2 / (8 * (2 + 3 * g * (d1 + d2))) := by
      unfold FL; simp only; rw [hndef]
      have hD' := hD.ne'
      rw [show 3 * g * (d1 + d2) = 3*(g*(d1+d2)) by ring]
      rw [show g*(d1+d2) = (1 - (1-g*d1)) + (1 - (1-g*d2)) by ring] at hD' ⊢
      generalize 1 - g*d1 = p at *
      generalize 1 - g*d2 = q at *
      generalize hE : 2 + 3 * (1 - p + (1 - q)) = E at *
      field_simp
      subst hE
      ring
    have key : ∀ y1 y3 : ℝ, FL ⟨d1,d2,g,c⟩ n n (2*n) - FL ⟨d1,d2,g,c⟩ y1 y1 y3 =
        (2 - g*(d1+d2))/2 * (y1 - n)^2 + g*(d1+d2)/2 * (y3 - 2*n)^2
        + g*(d1+d2)/2*(1 - 4*n)*(2*y1 - y3) := by
      intro y1 y3
      unfold FL; simp only
      linear_combination (y1 - n) * hn
    have hD2 : (0:ℝ) ≤ (2 - g*(d1+d2))/2 := by linarith
    refine ⟨⟨⟨⟨n, n⟩, ⟨by simp only; linarith, by simp only; linarith⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [profitLI_eq]; simp only; rw [← hval]; congr 1; ring
    · rintro v ⟨y, hy, rfl⟩
      obtain ⟨hu, hun⟩ := hy
      rw [profitLI_eq, ← hval]
      have := key y.n (y.n + y.u)
      have a1 := mul_nonneg hD2 (sq_nonneg (y.n - n))
      have a2 := mul_nonneg hB2 (sq_nonneg (y.n + y.u - 2*n))
      have a3 := mul_nonneg (mul_nonneg hB2 (by linarith : (0:ℝ) ≤ 1 - 4*n))
        (by linarith : (0:ℝ) ≤ 2*y.n - (y.n + y.u))
      linarith
    · intro x ⟨hx, hmax⟩
      obtain ⟨hu, hun⟩ := hx
      have hfe : (⟨n, n⟩ : LIQty) ∈ feasLI := ⟨by simp only; linarith, by simp only; linarith⟩
      have h1 := hmax _ hfe
      rw [profitLI_eq, profitLI_eq] at h1
      simp only at h1
      have e := key x.n (x.n + x.u)
      rw [show n + n = 2*n by ring] at h1
      have a1 := mul_nonneg hD2 (sq_nonneg (x.n - n))
      have a2 := mul_nonneg hB2 (sq_nonneg (x.n + x.u - 2*n))
      have a3 := mul_nonneg (mul_nonneg hB2 (by linarith : (0:ℝ) ≤ 1 - 4*n))
        (by linarith : (0:ℝ) ≤ 2*x.n - (x.n + x.u))
      have z1 : (2 - g*(d1+d2))/2 * (x.n - n)^2 = 0 := by linarith
      have z2 : g*(d1+d2)/2 * (x.n + x.u - 2*n)^2 = 0 := by linarith
      have e1 : x.n = n := by
        rcases mul_eq_zero.mp z1 with h3 | h3
        · linarith
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3; linarith
      have e2 : x.n + x.u = 2*n := by
        rcases mul_eq_zero.mp z2 with h3 | h3
        · linarith
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3; linarith
      constructor <;> linarith
