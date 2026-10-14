-- Prove2me | solution 1 for MDOUnifiedCosmology.potential_minimum
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:15:09.618977+00:00
-- url     : https://prove2.me/submissions/5ddeb984-70b4-4f56-917b-449d7a529dc2

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (A φc m α : ℝ) (hA : 0 < A) (hφc : 0 < φc)
    (hα : 0 < effCoupling A φc α) :
    ∀ φ : ℝ, potential A φc m α (phiMin A φc m α) ≤ potential A φc m α φ := by
  let r : ℝ := (1-m^2*φc^2/(4*A^4))/(1+α*φc^4/(4*A^4))
  have hd : 1+α*φc^4/(4*A^4) = φc^4/(4*A^4)*effCoupling A φc α := by
    unfold effCoupling
    field_simp
    ring
  have hdpos : 0 < 1+α*φc^4/(4*A^4) := by rw [hd]; positivity
  have he : (φc^2*effCoupling A φc α)*r = -effMassSq A φc m := by
    dsimp [r]
    rw [hd]
    field_simp [ne_of_gt hα]
    unfold effMassSq
    field_simp
    ring
  have hv (x : ℝ) : potential A φc m α x =
      effMassSq A φc m / 2 * x^2 + effCoupling A φc α / 4 * x^4 + A^4 := by
    unfold potential V1 V2 effMassSq effCoupling
    field_simp
    ring
  intro φ
  by_cases hr : 0 ≤ r
  · have hs : phiMin A φc m α ^ 2 = φc^2*r := by
      change (φc*Real.sqrt r)^2 = _
      rw [mul_pow, Real.sq_sqrt hr]
    have hx : effCoupling A φc α * phiMin A φc m α ^ 2 = -effMassSq A φc m := by
      rw [hs]
      nlinarith [he]
    have hz : effMassSq A φc m + effCoupling A φc α * phiMin A φc m α ^ 2 = 0 := by linarith
    have heq : potential A φc m α φ - potential A φc m α (phiMin A φc m α) =
        effCoupling A φc α / 4 * (φ^2-phiMin A φc m α^2)^2 := by
      calc
        _ = effCoupling A φc α / 4 * (φ^2-phiMin A φc m α^2)^2 +
            (effMassSq A φc m + effCoupling A φc α * phiMin A φc m α ^ 2) / 2 *
            (φ^2-phiMin A φc m α^2) := by rw [hv, hv]; ring
        _ = _ := by rw [hz]; ring
    have hn : 0 ≤ effCoupling A φc α / 4 * (φ^2-phiMin A φc m α^2)^2 := by positivity
    linarith
  · have hrn : r ≤ 0 := le_of_lt (lt_of_not_ge hr)
    have hz : phiMin A φc m α = 0 := by
      change φc*Real.sqrt r = 0
      rw [Real.sqrt_eq_zero_of_nonpos hrn, mul_zero]
    have hb : 0 ≤ effMassSq A φc m := by
      have hn := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (sq_nonneg φc) hα.le) hrn
      rw [he] at hn
      linarith
    rw [hz, hv, hv]
    norm_num
    positivity




