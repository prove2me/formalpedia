-- Prove2me | solution 1 for ImpulseGames.LinearGame.eq_4_17_unique_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:37:54.306227+00:00
-- url     : https://prove2.me/submissions/9395f75c-ec0d-4495-8d6d-11b57c4af78c

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Candidates

namespace ImpulseGames.LinearGame

lemma eta_pos_81fa (M : Model) (hM : M.Standing) : 0 < eta M := by
  unfold eta; exact div_pos hM.one_sub_lam_mul_ρ_pos hM.ρ_pos

lemma theta_pos_81fa (M : Model) (hM : M.Standing) : 0 < theta M := by
  unfold theta
  have := hM.σ_pos
  have := hM.ρ_pos
  apply Real.sqrt_pos.mpr
  positivity

lemma F_hasDerivAt_81fa (M : Model) {y : ℝ} (h0 : -eta M < y) (h1 : y < eta M) :
    HasDerivAt (F M) (2 - eta M * ((((1:ℝ) * (eta M - y) - (eta M + y) * (-1)) / (eta M - y) ^ 2)
      / ((eta M + y) / (eta M - y)))) y := by
  have hne : eta M - y ≠ 0 := by
    have : 0 < eta M - y := by linarith
    exact this.ne'
  have hq : HasDerivAt (fun x => (eta M + x) / (eta M - x))
      (((1:ℝ) * (eta M - y) - (eta M + y) * (-1)) / (eta M - y) ^ 2) y := by
    apply HasDerivAt.div
    · simpa using (hasDerivAt_id y).const_add (eta M)
    · simpa using (hasDerivAt_id y).const_sub (eta M)
    · exact hne
  have hpos : (eta M + y) / (eta M - y) ≠ 0 :=
    (div_pos (by linarith) (by linarith)).ne'
  have hl := hq.log hpos
  have h2 := (((hasDerivAt_id y).const_mul (2:ℝ)).add_const (theta M * M.c)).sub (hl.const_mul (eta M))
  have e : F M = (fun x => 2 * id x + theta M * M.c)
      - fun y => eta M * Real.log ((eta M + y) / (eta M - y)) := by
    funext x; simp [F]
  rw [e]
  rw [mul_one] at h2
  exact h2

lemma F_deriv_neg_81fa (M : Model) (hM : M.Standing) {y : ℝ} (h0 : 0 < y) (h1 : y < eta M) :
    deriv (F M) y < 0 := by
  have he := eta_pos_81fa M hM
  rw [(F_hasDerivAt_81fa M (by linarith) h1).deriv]
  have ha : 0 < eta M - y := by linarith
  have hb : 0 < eta M + y := by linarith
  have key : eta M * ((((1:ℝ) * (eta M - y) - (eta M + y) * (-1)) / (eta M - y) ^ 2)
      / ((eta M + y) / (eta M - y))) = 2 * eta M ^ 2 / ((eta M - y) * (eta M + y)) := by
    field_simp
    ring
  rw [key, sub_neg, lt_div_iff₀ (by positivity)]
  nlinarith

end ImpulseGames.LinearGame

open ImpulseGames.LinearGame in
theorem solution (M : Model) (hM : M.Standing) (hc : 0 < M.c) :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo 0 (eta M) ∧ F M ξ = 0 := by
  have he := eta_pos_81fa M hM
  have ht := theta_pos_81fa M hM
  -- strict antitonicity on (0, η)
  have hanti : StrictAntiOn (F M) (Set.Ioo 0 (eta M)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (eta M))
    · intro x hx
      exact (F_hasDerivAt_81fa M (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact F_deriv_neg_81fa M hM hx.1 hx.2
  -- a point b with F b < 0
  set K : ℝ := (2 * eta M + theta M * M.c) / eta M + 1 with hK
  have hKpos : 0 < K := by
    have : 0 < (2 * eta M + theta M * M.c) / eta M := by
      apply div_pos _ he; nlinarith
    linarith
  set E : ℝ := Real.exp K with hE
  have hE1 : 1 < E := by
    have := Real.add_one_lt_exp hKpos.ne'
    rw [hE]; linarith
  set b : ℝ := eta M * (E - 1) / (E + 1) with hb
  have hb0 : 0 < b := by
    apply div_pos _ (by linarith); apply mul_pos he; linarith
  have hbη : b < eta M := by
    rw [hb, div_lt_iff₀ (by linarith)]; nlinarith
  have hratio : (eta M + b) / (eta M - b) = E := by
    rw [hb]
    have : E + 1 ≠ 0 := by linarith
    field_simp
    ring
  have hFb : F M b < 0 := by
    have : F M b = 2 * b + theta M * M.c - eta M * K := by
      simp only [F]; rw [hratio, hE, Real.log_exp]
    rw [this]
    have : eta M * K = 2 * eta M + theta M * M.c + eta M := by
      rw [hK]; field_simp
    rw [this]; linarith
  have hF0 : 0 < F M 0 := by
    simp only [F]
    rw [add_zero, sub_zero, div_self he.ne', Real.log_one]
    have := mul_pos ht hc
    linarith
  have hcont : ContinuousOn (F M) (Set.Icc 0 b) := by
    intro x hx
    exact (F_hasDerivAt_81fa M (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
  obtain ⟨ξ, ⟨hξ0, hξb⟩, hξ⟩ :=
    intermediate_value_Icc' hb0.le hcont (show (0:ℝ) ∈ Set.Icc (F M b) (F M 0) from ⟨hFb.le, hF0.le⟩)
  have hξpos : 0 < ξ := by
    rcases lt_or_eq_of_le hξ0 with h | h
    · exact h
    · subst h; linarith
  have hmem : ξ ∈ Set.Ioo 0 (eta M) := ⟨hξpos, by linarith⟩
  refine ⟨ξ, ⟨hmem, hξ⟩, ?_⟩
  rintro y ⟨hy, hFy⟩
  exact hanti.injOn hy hmem (hFy.trans hξ.symm)
