-- Prove2me | solution 1 for LeaseModular.JointChoice.pi_SM_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:04:23.034643+00:00
-- url     : https://prove2.me/submissions/fdec372d-042e-4ab9-817c-fb485d31e371

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

open LeaseModular.JointChoice

theorem solution (P : Params) (hP : Standing P) :
    (P.c ≤ CSM P.δ₁ P.δ₂ →
      IsOptSM P ((1 / 8) * ((1 - 2 * P.c - P.δ₂) ^ 2 / (1 - P.δ₂) +
        (1 - 2 * P.c + 2 * P.δ₂ + P.δ₁) ^ 2 / (1 + 3 * P.δ₁ + 4 * P.δ₂)))) ∧
    (P.c < CSM P.δ₁ P.δ₂ → ∀ x, IsMaxSM P x → x.n1 < x.n2) ∧
    (CSM P.δ₁ P.δ₂ ≤ P.c →
      IsOptSM P ((2 - 4 * P.c + P.δ₁ + P.δ₂) ^ 2 / (8 * (2 + 3 * (P.δ₁ + P.δ₂))))) := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl⟩ := hP
  simp only at *
  have hK : 0 < 3*d1+5*d2 := by linarith
  have hr : 0 < 1 - d2 := by linarith
  have hA : 0 < 1 + 3*d1 + 4*d2 := by linarith
  set x := ((1+d1+2*d2)/2 - c)/(1 + 3*d1 + 4*d2) with hxdef
  set t := ((1-d2)/2 - c)/(1-d2) with htdef
  have hx : (1 + 3*d1 + 4*d2)*x = (1+d1+2*d2)/2 - c := mul_div_cancel₀ _ hA.ne'
  have ht : (1-d2)*t = (1-d2)/2 - c := mul_div_cancel₀ _ hr.ne'
  have keyW : ∀ y : SMQty, profitSM ⟨d1,d2,g,c⟩ ⟨x, t⟩ - profitSM ⟨d1,d2,g,c⟩ y =
      (1 + 3*d1 + 4*d2)/2 * (y.n1 - x)^2 + (1-d2)/2 * (y.n2 - t)^2 := by
    intro y; unfold profitSM pSM1 pSM2; simp only
    linear_combination (y.n1 - x)*hx + (y.n2 - t)*ht
  have hvalW : profitSM ⟨d1,d2,g,c⟩ ⟨x, t⟩ = (1 / 8) * ((1 - 2 * c - d2) ^ 2 / (1 - d2) +
        (1 - 2 * c + 2 * d2 + d1) ^ 2 / (1 + 3 * d1 + 4 * d2)) := by
    unfold profitSM pSM1 pSM2; simp only; rw [hxdef, htdef]
    have hA' := hA.ne'
    have hr' := hr.ne'
    generalize hE : 1 + 3*d1 + 4*d2 = E at *
    generalize hR : 1 - d2 = R at *
    field_simp
    subst hE hR
    ring
  have hpos := mul_pos hA hr
  have ext : (1 + 3*d1 + 4*d2)*(1-d2)*(t - x) = (1-d2)*(d1+d2) - c*(3*d1+5*d2) := by
    linear_combination (1 + 3*d1 + 4*d2)*ht - (1-d2)*hx
  have hx0 : 0 ≤ x := by
    by_contra hh; push Not at hh
    have := mul_neg_of_pos_of_neg hA hh; linarith
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h' : c*(3*d1+5*d2) ≤ (1-d2)*(d1+d2) := by
      unfold CSM at h; rwa [le_div_iff₀ hK] at h
    have hxt : x ≤ t := by
      by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hpos (by linarith : t - x < 0); linarith
    refine ⟨⟨⟨x, t⟩, ⟨hx0, hxt⟩, hvalW⟩, ?_⟩
    rintro v ⟨y, _, rfl⟩
    have := keyW y
    have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 + 3*d1 + 4*d2)/2) (sq_nonneg (y.n1 - x))
    have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d2)/2) (sq_nonneg (y.n2 - t))
    linarith
  · have h' : c*(3*d1+5*d2) < (1-d2)*(d1+d2) := by
      unfold CSM at h; rwa [lt_div_iff₀ hK] at h
    have hxt : x < t := by
      by_contra hh; push Not at hh
      have := mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith : t - x ≤ 0); linarith
    intro y ⟨_, hmax⟩
    have h1 := hmax ⟨x, t⟩ ⟨hx0, hxt.le⟩
    have := keyW y
    have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 + 3*d1 + 4*d2)/2) (sq_nonneg (y.n1 - x))
    have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d2)/2) (sq_nonneg (y.n2 - t))
    have z1 : (1 + 3*d1 + 4*d2)/2 * (y.n1 - x)^2 = 0 := by linarith
    have z2 : (1 - d2)/2 * (y.n2 - t)^2 = 0 := by linarith
    have e1 : y.n1 = x := by
      rcases mul_eq_zero.mp z1 with h3 | h3
      · linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3; linarith
    have e2 : y.n2 = t := by
      rcases mul_eq_zero.mp z2 with h3 | h3
      · linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3; linarith
    rw [e1, e2]; exact hxt
  · have h' : (1-d2)*(d1+d2) ≤ c*(3*d1+5*d2) := by
      unfold CSM at h; rwa [div_le_iff₀ hK] at h
    have hD : 0 < 2 + 3*(d1+d2) := by linarith
    set S := (1 + (d1+d2)/2 - 2*c)/(2 + 3*(d1+d2)) with hSdef
    have hS : (2 + 3*(d1+d2))*S = 1 + (d1+d2)/2 - 2*c := mul_div_cancel₀ _ hD.ne'
    have hS0 : 0 ≤ S := by
      by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hD hh; linarith
    have hgt : 0 ≤ (1-d2)*S - ((1-d2)/2 - c) := by
      have e : (2 + 3*(d1+d2))*((1-d2)*S - ((1-d2)/2 - c)) =
          c*(3*d1+5*d2) - (1-d2)*(d1+d2) := by
        linear_combination (1-d2)*hS
      by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hD hh; linarith
    have keyD : ∀ y : SMQty, profitSM ⟨d1,d2,g,c⟩ ⟨S, S⟩ - profitSM ⟨d1,d2,g,c⟩ y =
        (1 + 3*d1 + 4*d2)/2 * (y.n1 - S)^2 + (1-d2)/2 * (y.n2 - S)^2
        + ((1-d2)*S - ((1-d2)/2 - c))*(y.n2 - y.n1) := by
      intro y; unfold profitSM pSM1 pSM2; simp only
      linear_combination (y.n1 - S)*hS
    have hvalD : profitSM ⟨d1,d2,g,c⟩ ⟨S, S⟩ = (2 - 4 * c + d1 + d2) ^ 2 / (8 * (2 + 3 * (d1 + d2))) := by
      unfold profitSM pSM1 pSM2; simp only; rw [hSdef]
      have hD' := hD.ne'
      generalize hE : 2 + 3*(d1+d2) = E at *
      field_simp
      subst hE
      ring
    refine ⟨⟨⟨S, S⟩, ⟨hS0, le_rfl⟩, hvalD⟩, ?_⟩
    rintro v ⟨y, ⟨_, hy12⟩, rfl⟩
    have := keyD y
    have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 + 3*d1 + 4*d2)/2) (sq_nonneg (y.n1 - S))
    have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d2)/2) (sq_nonneg (y.n2 - S))
    have a3 := mul_nonneg hgt (by linarith : (0:ℝ) ≤ y.n2 - y.n1)
    linarith
