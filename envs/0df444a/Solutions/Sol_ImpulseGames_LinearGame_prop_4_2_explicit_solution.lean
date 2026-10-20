-- Prove2me | solution 1 for ImpulseGames.LinearGame.prop_4_2_explicit_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T14:58:45.263696+00:00
-- url     : https://prove2.me/submissions/90a125bc-73ea-4fb0-a7b2-c6fae1fe8e1c

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Candidates

set_option autoImplicit false

namespace P5f0a

open ImpulseGames.LinearGame Real

section Ev
variable (M : Model) (ξ s : ℝ)

noncomputable def d1One (y : ℝ) : ℝ :=
  theta M * A M ξ s 1 1 * exp (theta M * y) - theta M * A M ξ s 1 2 * exp (-(theta M * y)) + 1 / M.ρ

noncomputable def d2One (y : ℝ) : ℝ :=
  theta M ^ 2 * (A M ξ s 1 1 * exp (theta M * y) + A M ξ s 1 2 * exp (-(theta M * y)))

noncomputable def d1Two (y : ℝ) : ℝ :=
  theta M * A M ξ s 2 1 * exp (theta M * y) - theta M * A M ξ s 2 2 * exp (-(theta M * y)) - 1 / M.ρ

noncomputable def d2Two (y : ℝ) : ℝ :=
  theta M ^ 2 * (A M ξ s 2 1 * exp (theta M * y) + A M ξ s 2 2 * exp (-(theta M * y)))

lemma hasDerivAt_e1 (y : ℝ) :
    HasDerivAt (fun y => exp (theta M * y)) (exp (theta M * y) * theta M) y := by
  simpa using ((hasDerivAt_id' y).const_mul (theta M)).exp

lemma hasDerivAt_e2 (y : ℝ) :
    HasDerivAt (fun y => exp (-(theta M * y))) (exp (-(theta M * y)) * -theta M) y := by
  simpa using (((hasDerivAt_id' y).const_mul (theta M)).neg).exp

lemma hasDerivAt_phiOne (y : ℝ) : HasDerivAt (phiOne M ξ s) (d1One M ξ s y) y := by
  unfold phiOne phi1 d1One
  have h3 : HasDerivAt (fun y => (y - M.s₁) / M.ρ) (1 / M.ρ) y := by
    simpa using ((hasDerivAt_id' y).sub_const M.s₁).div_const M.ρ
  exact ((((hasDerivAt_e1 M y).const_mul (A M ξ s 1 1)).add
    ((hasDerivAt_e2 M y).const_mul (A M ξ s 1 2))).add h3).congr_deriv (by ring)

lemma hasDerivAt_d1One (y : ℝ) : HasDerivAt (d1One M ξ s) (d2One M ξ s y) y := by
  unfold d1One d2One
  exact ((((hasDerivAt_e1 M y).const_mul (theta M * A M ξ s 1 1)).sub
    ((hasDerivAt_e2 M y).const_mul (theta M * A M ξ s 1 2))).add_const (1 / M.ρ)).congr_deriv
    (by ring)

lemma hasDerivAt_phiTwo (y : ℝ) : HasDerivAt (phiTwo M ξ s) (d1Two M ξ s y) y := by
  unfold phiTwo phi2 d1Two
  have h3 : HasDerivAt (fun y => (M.s₂ - y) / M.ρ) (-1 / M.ρ) y := by
    simpa using ((hasDerivAt_id' y).const_sub M.s₂).div_const M.ρ
  exact ((((hasDerivAt_e1 M y).const_mul (A M ξ s 2 1)).add
    ((hasDerivAt_e2 M y).const_mul (A M ξ s 2 2))).add h3).congr_deriv (by ring)

lemma hasDerivAt_d1Two (y : ℝ) : HasDerivAt (d1Two M ξ s) (d2Two M ξ s y) y := by
  unfold d1Two d2Two
  exact ((((hasDerivAt_e1 M y).const_mul (theta M * A M ξ s 2 1)).sub
    ((hasDerivAt_e2 M y).const_mul (theta M * A M ξ s 2 2))).sub_const (1 / M.ρ)).congr_deriv
    (by ring)

lemma deriv_phiOne (y : ℝ) : deriv (phiOne M ξ s) y = d1One M ξ s y :=
  (hasDerivAt_phiOne M ξ s y).deriv

lemma deriv2_phiOne (y : ℝ) : deriv (deriv (phiOne M ξ s)) y = d2One M ξ s y := by
  have : deriv (phiOne M ξ s) = d1One M ξ s := funext (deriv_phiOne M ξ s)
  rw [this]; exact (hasDerivAt_d1One M ξ s y).deriv

lemma deriv_phiTwo (y : ℝ) : deriv (phiTwo M ξ s) y = d1Two M ξ s y :=
  (hasDerivAt_phiTwo M ξ s y).deriv

lemma deriv2_phiTwo (y : ℝ) : deriv (deriv (phiTwo M ξ s)) y = d2Two M ξ s y := by
  have : deriv (phiTwo M ξ s) = d1Two M ξ s := funext (deriv_phiTwo M ξ s)
  rw [this]; exact (hasDerivAt_d1Two M ξ s y).deriv

/-- shared rewriting for the evaluation lemmas -/
lemma exp_shift (hθ : theta M ≠ 0) (t : ℝ) :
    exp (theta M * (s + t / theta M)) = exp (theta M * s) * exp t ∧
    exp (-(theta M * (s + t / theta M))) = (exp (theta M * s))⁻¹ * exp (-t) ∧
    exp ((-1 : ℝ) ^ 1 * theta M * s) = (exp (theta M * s))⁻¹ ∧
    exp ((-1 : ℝ) ^ 2 * theta M * s) = exp (theta M * s) := by
  have h1 : theta M * (s + t / theta M) = theta M * s + t := by field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, exp_add]
  · rw [h1, neg_add, exp_add, exp_neg]
  · rw [← exp_neg]; ring_nf
  · ring_nf

lemma phiOne_eval (hθ : theta M ≠ 0) (t : ℝ) :
    phiOne M ξ s (s + t / theta M) =
      √(eta M ^ 2 - ξ ^ 2) / (2 * theta M) *
        (-((√(Gam M ξ + 1) + √(Gam M ξ)) * exp t) + (√(Gam M ξ + 1) - √(Gam M ξ)) * exp (-t))
      + (s + t / theta M - M.s₁) / M.ρ := by
  obtain ⟨e1, e2, e3, e4⟩ := exp_shift M s hθ t
  have hE := (exp_pos (theta M * s)).ne'
  unfold phiOne phi1 A
  rw [e1, e2, e3, e4]
  field_simp
  ring

lemma d1One_eval (hθ : theta M ≠ 0) (t : ℝ) :
    d1One M ξ s (s + t / theta M) =
      theta M * (√(eta M ^ 2 - ξ ^ 2) / (2 * theta M)) *
        (-((√(Gam M ξ + 1) + √(Gam M ξ)) * exp t) - (√(Gam M ξ + 1) - √(Gam M ξ)) * exp (-t))
      + 1 / M.ρ := by
  obtain ⟨e1, e2, e3, e4⟩ := exp_shift M s hθ t
  have hE := (exp_pos (theta M * s)).ne'
  unfold d1One A
  rw [e1, e2, e3, e4]
  field_simp
  ring

lemma d2One_eval (hθ : theta M ≠ 0) (t : ℝ) :
    d2One M ξ s (s + t / theta M) =
      theta M ^ 2 * (√(eta M ^ 2 - ξ ^ 2) / (2 * theta M)) *
        (-((√(Gam M ξ + 1) + √(Gam M ξ)) * exp t) + (√(Gam M ξ + 1) - √(Gam M ξ)) * exp (-t)) := by
  obtain ⟨e1, e2, e3, e4⟩ := exp_shift M s hθ t
  have hE := (exp_pos (theta M * s)).ne'
  unfold d2One A
  rw [e1, e2, e3, e4]
  field_simp
  ring

lemma phiTwo_eval (hθ : theta M ≠ 0) (t : ℝ) :
    phiTwo M ξ s (s + t / theta M) =
      √(eta M ^ 2 - ξ ^ 2) / (2 * theta M) *
        ((√(Gam M ξ + 1) - √(Gam M ξ)) * exp t - (√(Gam M ξ + 1) + √(Gam M ξ)) * exp (-t))
      + (M.s₂ - (s + t / theta M)) / M.ρ := by
  obtain ⟨e1, e2, e3, e4⟩ := exp_shift M s hθ t
  have hE := (exp_pos (theta M * s)).ne'
  unfold phiTwo phi2 A
  rw [e1, e2, e3, e4]
  field_simp
  ring

lemma d1Two_eval (hθ : theta M ≠ 0) (t : ℝ) :
    d1Two M ξ s (s + t / theta M) =
      theta M * (√(eta M ^ 2 - ξ ^ 2) / (2 * theta M)) *
        ((√(Gam M ξ + 1) - √(Gam M ξ)) * exp t + (√(Gam M ξ + 1) + √(Gam M ξ)) * exp (-t))
      - 1 / M.ρ := by
  obtain ⟨e1, e2, e3, e4⟩ := exp_shift M s hθ t
  have hE := (exp_pos (theta M * s)).ne'
  unfold d1Two A
  rw [e1, e2, e3, e4]
  field_simp
  ring

lemma d2Two_eval (hθ : theta M ≠ 0) (t : ℝ) :
    d2Two M ξ s (s + t / theta M) =
      theta M ^ 2 * (√(eta M ^ 2 - ξ ^ 2) / (2 * theta M)) *
        ((√(Gam M ξ + 1) - √(Gam M ξ)) * exp t - (√(Gam M ξ + 1) + √(Gam M ξ)) * exp (-t)) := by
  obtain ⟨e1, e2, e3, e4⟩ := exp_shift M s hθ t
  have hE := (exp_pos (theta M * s)).ne'
  unfold d2Two A
  rw [e1, e2, e3, e4]
  field_simp
  ring

lemma Gam_pos (hM : M.Standing) (hc : 0 < M.c) (hξ0 : 0 < ξ) : 0 < Gam M ξ := by
  have hθ : 0 < theta M := Real.sqrt_pos.2 (by have := hM.σ_pos; have := hM.ρ_pos; positivity)
  have hη : 0 < eta M := div_pos hM.one_sub_lam_mul_ρ_pos hM.ρ_pos
  unfold Gam
  have h1 : 0 ≤ M.c - M.ct := by linarith [hM.ct_le_c]
  have h2 : 0 ≤ M.lam - M.lamt := by linarith [hM.lamt_le_lam]
  have t1 : 0 ≤ theta M * (M.c - M.ct) / (4 * ξ) := by positivity
  have t2 : 0 ≤ theta M * M.c * (M.lam - M.lamt) / (4 * eta M * ξ) := by positivity
  have t3 : 0 ≤ (M.lam - M.lamt) / (2 * eta M) := by positivity
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · have : 0 < theta M * (M.c - M.ct) / (4 * ξ) := by positivity
    linarith
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · have : 0 < (M.lam - M.lamt) / (2 * eta M) := by positivity
      linarith
    · exfalso; apply hM.costs_ne
      have e1 : M.c = M.ct := by linarith
      have e2 : M.lam = M.lamt := by linarith
      rw [e1, e2]

end Ev

end P5f0a

open ImpulseGames.LinearGame in
theorem solution (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 (eta M)) (hFξ : F M ξ = 0) (s : ℝ) :
    -- (4.7)
    (xbar M ξ s 1 < xstar M ξ s 1 ∧ xstar M ξ s 1 < xbar M ξ s 2) ∧
    (xbar M ξ s 1 < xstar M ξ s 2 ∧ xstar M ξ s 2 < xbar M ξ s 2) ∧
    -- (4.8a)
    (deriv (phiOne M ξ s) (xstar M ξ s 1) = M.lam ∧
      deriv (deriv (phiOne M ξ s)) (xstar M ξ s 1) ≤ 0) ∧
    -- (4.8b)
    deriv (phiOne M ξ s) (xbar M ξ s 1) = M.lam ∧
    -- (4.8c)
    phiOne M ξ s (xbar M ξ s 1) =
      phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - xbar M ξ s 1) ∧
    -- (4.8d)
    phiOne M ξ s (xbar M ξ s 2) =
      phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (xbar M ξ s 2 - xstar M ξ s 2) ∧
    -- (4.9a)
    (deriv (phiTwo M ξ s) (xstar M ξ s 2) = -M.lam ∧
      deriv (deriv (phiTwo M ξ s)) (xstar M ξ s 2) ≤ 0) ∧
    -- (4.9b)
    deriv (phiTwo M ξ s) (xbar M ξ s 2) = -M.lam ∧
    -- (4.9c)
    phiTwo M ξ s (xbar M ξ s 1) =
      phiTwo M ξ s (xstar M ξ s 1) + M.ct + M.lamt * (xstar M ξ s 1 - xbar M ξ s 1) ∧
    -- (4.9d)
    phiTwo M ξ s (xbar M ξ s 2) =
      phiTwo M ξ s (xstar M ξ s 2) - M.c - M.lam * (xbar M ξ s 2 - xstar M ξ s 2) ∧
    -- the inflection point of φ₂
    (∃ xt ∈ Set.Ioo (xstar M ξ s 2) (xbar M ξ s 2),
      (∀ y ∈ Set.Ioo (xbar M ξ s 1) xt, deriv (deriv (phiTwo M ξ s)) y < 0) ∧
      (∀ y ∈ Set.Ioo xt (xbar M ξ s 2), 0 < deriv (deriv (phiTwo M ξ s)) y)) := by
  obtain ⟨hξ0, hξη⟩ := hξ
  have hρ := hM.ρ_pos
  have hθ : 0 < theta M := Real.sqrt_pos.2 (by have := hM.σ_pos; positivity)
  have hθ0 : theta M ≠ 0 := hθ.ne'
  have hη : 0 < eta M := div_pos hM.one_sub_lam_mul_ρ_pos hρ
  have hΓ : 0 < Gam M ξ := P5f0a.Gam_pos M ξ hM hc hξ0
  have hpq : 0 < eta M - ξ := by linarith
  have hpp : 0 < eta M + ξ := by linarith
  -- algebraic facts (before abstraction)
  have hlam : M.lam = 1 / M.ρ - eta M := by unfold eta; field_simp; ring
  have hF' : 2 * ξ * (theta M)⁻¹ + M.c
      - eta M * Real.log ((eta M + ξ) / (eta M - ξ)) * (theta M)⁻¹ = 0 := by
    unfold F at hFξ
    field_simp
    linear_combination hFξ
  have hDη : Real.log ((eta M + ξ) / (eta M - ξ)) * (theta M)⁻¹
      = (2 * ξ * (theta M)⁻¹ + M.c) * (eta M)⁻¹ := by
    unfold F at hFξ
    field_simp
    linear_combination (-1) * hFξ
  have hΓ'' : 4 * ξ * Gam M ξ * (theta M)⁻¹ = (M.c - M.ct) + M.c * (M.lam - M.lamt) * (eta M)⁻¹
      + 2 * ξ * (M.lam - M.lamt) * (theta M)⁻¹ * (eta M)⁻¹ := by
    unfold Gam
    field_simp
    ring
  -- the square roots
  have hr1 : 1 < √((eta M + ξ) / (eta M - ξ)) := by
    rw [Real.lt_sqrt (by norm_num), one_pow, one_lt_div hpq]; linarith
  have hri : √((eta M - ξ) / (eta M + ξ)) = (√((eta M + ξ) / (eta M - ξ)))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  have hr2 : (√((eta M + ξ) / (eta M - ξ))) ^ 2 = (eta M + ξ) / (eta M - ξ) :=
    Real.sq_sqrt (by positivity)
  have hu : √(eta M ^ 2 - ξ ^ 2) = (eta M - ξ) * √((eta M + ξ) / (eta M - ξ)) := by
    rw [show eta M ^ 2 - ξ ^ 2 = (eta M - ξ) ^ 2 * ((eta M + ξ) / (eta M - ξ)) by field_simp; ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpq.le]
  have hG1 : (√(Gam M ξ + 1)) ^ 2 = Gam M ξ + 1 := Real.sq_sqrt (by linarith)
  have hG0 : (√(Gam M ξ)) ^ 2 = Gam M ξ := Real.sq_sqrt hΓ.le
  have hG0p : 0 < √(Gam M ξ) := Real.sqrt_pos.2 hΓ
  have hG1g : 1 ≤ √(Gam M ξ + 1) := Real.one_le_sqrt.2 (by linarith)
  have hGlt : √(Gam M ξ) < √(Gam M ξ + 1) := Real.sqrt_lt_sqrt hΓ.le (by linarith)
  -- points
  have hx1b : xbar M ξ s 1 = s + (-Real.log (√((eta M + ξ) / (eta M - ξ)) *
      (√(Gam M ξ + 1) + √(Gam M ξ)))) / theta M := by unfold xbar; ring
  have hx2b : xbar M ξ s 2 = s + (Real.log (√((eta M + ξ) / (eta M - ξ)) *
      (√(Gam M ξ + 1) + √(Gam M ξ)))) / theta M := by unfold xbar; ring
  have hx1s : xstar M ξ s 1 = s + (-Real.log (√((eta M - ξ) / (eta M + ξ)) *
      (√(Gam M ξ + 1) + √(Gam M ξ)))) / theta M := by unfold xstar; ring
  have hx2s : xstar M ξ s 2 = s + (Real.log (√((eta M - ξ) / (eta M + ξ)) *
      (√(Gam M ξ + 1) + √(Gam M ξ)))) / theta M := by unfold xstar; ring
  have hD : Real.log (√((eta M + ξ) / (eta M - ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ)))
      - Real.log (√((eta M - ξ) / (eta M + ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ)))
      = Real.log ((eta M + ξ) / (eta M - ξ)) := by
    have h2 : Real.log ((eta M + ξ) / (eta M - ξ)) = 2 * Real.log (√((eta M + ξ) / (eta M - ξ))) := by
      conv_lhs => rw [← hr2]
      rw [Real.log_pow]; push_cast; ring
    rw [hri, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_inv, h2]
    ring
  have hLR : Real.log (√((eta M + ξ) / (eta M - ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ)))
      = Real.log (√((eta M + ξ) / (eta M - ξ))) + Real.log (√(Gam M ξ + 1) + √(Gam M ξ)) :=
    Real.log_mul (by positivity) (by positivity)
  have hLS : Real.log (√((eta M - ξ) / (eta M + ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ)))
      = -Real.log (√((eta M + ξ) / (eta M - ξ))) + Real.log (√(Gam M ξ + 1) + √(Gam M ξ)) := by
    rw [hri, Real.log_mul (by positivity) (by positivity), Real.log_inv]
  have eLR : Real.exp (Real.log (√((eta M + ξ) / (eta M - ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ))))
      = √((eta M + ξ) / (eta M - ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ)) :=
    Real.exp_log (by positivity)
  have eLS : Real.exp (Real.log (√((eta M - ξ) / (eta M + ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ))))
      = (√((eta M + ξ) / (eta M - ξ)))⁻¹ * (√(Gam M ξ + 1) + √(Gam M ξ)) := by
    rw [Real.exp_log (by positivity), hri]
  have hK3 : (√(Gam M ξ + 1) + √(Gam M ξ)) * (√(Gam M ξ + 1) - √(Gam M ξ)) = 1 := by
    linear_combination hG1 - hG0
  have hginv : (√(Gam M ξ + 1) + √(Gam M ξ))⁻¹ = √(Gam M ξ + 1) - √(Gam M ξ) :=
    inv_eq_of_mul_eq_one_right hK3
  have eLRn : Real.exp (-Real.log (√((eta M + ξ) / (eta M - ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ))))
      = (√((eta M + ξ) / (eta M - ξ)))⁻¹ * (√(Gam M ξ + 1) - √(Gam M ξ)) := by
    rw [Real.exp_neg, eLR, mul_inv, hginv]
  have eLSn : Real.exp (-Real.log (√((eta M - ξ) / (eta M + ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ))))
      = √((eta M + ξ) / (eta M - ξ)) * (√(Gam M ξ + 1) - √(Gam M ξ)) := by
    rw [Real.exp_neg, eLS, mul_inv, inv_inv, hginv]
  have hlr : 0 < Real.log (√((eta M + ξ) / (eta M - ξ))) := Real.log_pos hr1
  have hlg : 0 < Real.log (√(Gam M ξ + 1) + √(Gam M ξ)) := Real.log_pos (by linarith)
  -- rewrite all the evaluation points
  have ev1 := P5f0a.phiOne_eval M ξ s hθ0
  have ev2 := P5f0a.d1One_eval M ξ s hθ0
  have ev3 := P5f0a.d2One_eval M ξ s hθ0
  have ev4 := P5f0a.phiTwo_eval M ξ s hθ0
  have ev5 := P5f0a.d1Two_eval M ξ s hθ0
  have ev6 := P5f0a.d2Two_eval M ξ s hθ0
  have dd1 := P5f0a.deriv_phiOne M ξ s
  have dd2 := P5f0a.deriv2_phiOne M ξ s
  have dd3 := P5f0a.deriv_phiTwo M ξ s
  have dd4 := P5f0a.deriv2_phiTwo M ξ s
  -- abstract
  generalize hLRd : Real.log (√((eta M + ξ) / (eta M - ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ))) = LR
    at hx1b hx2b hD hLR eLR eLRn
  generalize hLSd : Real.log (√((eta M - ξ) / (eta M + ξ)) * (√(Gam M ξ + 1) + √(Gam M ξ))) = LS
    at hx1s hx2s hD hLS eLS eLSn
  generalize hDd : Real.log ((eta M + ξ) / (eta M - ξ)) = D at hD hF' hDη
  generalize hQd : √(eta M ^ 2 - ξ ^ 2) / (2 * theta M) = Q at ev1 ev2 ev3 ev4 ev5 ev6
  have hθQ : theta M * Q = (eta M - ξ) * √((eta M + ξ) / (eta M - ξ)) / 2 := by
    rw [← hQd, hu]; field_simp
  have hQpos : 0 < Q := by
    rw [← hQd]
    have : 0 < eta M ^ 2 - ξ ^ 2 := by
      rw [show eta M ^ 2 - ξ ^ 2 = (eta M - ξ) * (eta M + ξ) by ring]; exact mul_pos hpq hpp
    positivity
  generalize hrd : √((eta M + ξ) / (eta M - ξ)) = r at *
  generalize hG1d : √(Gam M ξ + 1) = G1 at *
  generalize hG0d : √(Gam M ξ) = G0 at *
  have hr0 : 0 < r := by linarith
  have hr2' : r ^ 2 * (eta M - ξ) = eta M + ξ := by rw [hr2]; field_simp
  have hK1 : theta M * Q * (r + r⁻¹) = eta M := by
    rw [hθQ]; field_simp; linear_combination hr2'
  have hK2 : theta M * Q * (r - r⁻¹) = ξ := by
    rw [hθQ]; field_simp; linear_combination hr2'
  have hK2' : Q * (r - r⁻¹) = ξ * (theta M)⁻¹ := by
    rw [← hK2]; field_simp
  have hlam' := hlam
  have hpos2 : 0 < theta M * ξ := mul_pos hθ hξ0
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hx1b, hx1s]
    have : -LR / theta M < -LS / theta M := (div_lt_div_iff_of_pos_right hθ).2 (by linarith)
    linarith
  · rw [hx1s, hx2b]
    have : -LS / theta M < LR / theta M := (div_lt_div_iff_of_pos_right hθ).2 (by linarith)
    linarith
  · rw [hx1b, hx2s]
    have : -LR / theta M < LS / theta M := (div_lt_div_iff_of_pos_right hθ).2 (by linarith)
    linarith
  · rw [hx2s, hx2b]
    have : LS / theta M < LR / theta M := (div_lt_div_iff_of_pos_right hθ).2 (by linarith)
    linarith
  · simp only [hx1s, dd1, ev2, neg_neg, eLS, eLSn]
    linear_combination (-(theta M * Q * (r + r⁻¹))) * hK3 - hK1 - hlam
  · simp only [hx1s, dd2, ev3, neg_neg, eLS, eLSn]
    refine le_trans (le_of_eq ?_) (neg_nonpos.2 hpos2.le)
    linear_combination (theta M ^ 2 * Q * (r⁻¹ - r)) * hK3 - theta M * hK2
  · simp only [hx1b, dd1, ev2, neg_neg, eLR, eLRn]
    linear_combination (-(theta M * Q * (r + r⁻¹))) * hK3 - hK1 - hlam
  · simp only [hx1b, hx1s, ev1, neg_neg, eLR, eLRn, eLS, eLSn]
    linear_combination 2 * Q * (r - r⁻¹) * hK3 + 2 * hK2' + (LR - LS) * (theta M)⁻¹ * hlam
      - eta M * (theta M)⁻¹ * hD + hF'
  · simp only [hx2b, hx2s, ev1, eLR, eLRn, eLS, eLSn]
    linear_combination (-2 * Q * (r - r⁻¹)) * hG1 + (-2 * Q * (r - r⁻¹)) * hG0
      - (4 * Gam M ξ + 2) * hK2' + (theta M)⁻¹ * (1 / M.ρ - M.lamt) * hD - D * (theta M)⁻¹ * hlam
      - hF' + (M.lam - M.lamt) * hDη - hΓ''
  · simp only [hx2s, dd3, ev5, eLS, eLSn]
    linear_combination (theta M * Q * (r + r⁻¹)) * hK3 + hK1 + hlam
  · simp only [hx2s, dd4, ev6, eLS, eLSn]
    refine le_trans (le_of_eq ?_) (neg_nonpos.2 hpos2.le)
    linear_combination (theta M ^ 2 * Q * (r⁻¹ - r)) * hK3 - theta M * hK2
  · simp only [hx2b, dd3, ev5, eLR, eLRn]
    linear_combination (theta M * Q * (r + r⁻¹)) * hK3 + hK1 + hlam
  · simp only [hx1b, hx1s, ev4, neg_neg, eLR, eLRn, eLS, eLSn]
    linear_combination (-2 * Q * (r - r⁻¹)) * hG1 + (-2 * Q * (r - r⁻¹)) * hG0
      - (4 * Gam M ξ + 2) * hK2' + (theta M)⁻¹ * (1 / M.ρ - M.lamt) * hD - D * (theta M)⁻¹ * hlam
      - hF' + (M.lam - M.lamt) * hDη - hΓ''
  · simp only [hx2b, hx2s, ev4, eLR, eLRn, eLS, eLSn]
    linear_combination 2 * Q * (r - r⁻¹) * hK3 + 2 * hK2' + (LR - LS) * (theta M)⁻¹ * hlam
      - eta M * (theta M)⁻¹ * hD + hF'
  · have hg0 : 0 < G1 + G0 := by linarith
    have hm0 : 0 < G1 - G0 := by linarith
    have hθQp : 0 < theta M ^ 2 * Q := by positivity
    refine ⟨s + Real.log (G1 + G0) / theta M, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hx2s]
      have : LS / theta M < Real.log (G1 + G0) / theta M :=
        (div_lt_div_iff_of_pos_right hθ).2 (by linarith)
      linarith
    · rw [hx2b]
      have : Real.log (G1 + G0) / theta M < LR / theta M :=
        (div_lt_div_iff_of_pos_right hθ).2 (by linarith)
      linarith
    · intro y hy
      have h1 : y - s < Real.log (G1 + G0) / theta M := by linarith [hy.2]
      have ht : theta M * (y - s) < Real.log (G1 + G0) := by
        rw [lt_div_iff₀ hθ] at h1; linarith
      have hyy : y = s + theta M * (y - s) / theta M := by rw [mul_div_cancel_left₀ _ hθ0]; ring
      rw [dd4, hyy, ev6]
      have e1 : Real.exp (theta M * (y - s)) < G1 + G0 := by
        rw [← Real.exp_log hg0]; exact Real.exp_lt_exp.2 ht
      have e2 : G1 - G0 < Real.exp (-(theta M * (y - s))) := by
        rw [← hginv, Real.exp_neg]
        exact (inv_lt_inv₀ hg0 (Real.exp_pos _)).2 e1
      have p1 : (G1 - G0) * Real.exp (theta M * (y - s)) < 1 := by
        rw [← hK3, mul_comm (G1 + G0)]; exact mul_lt_mul_of_pos_left e1 hm0
      have p2 : 1 < (G1 + G0) * Real.exp (-(theta M * (y - s))) := by
        rw [← hK3]; exact mul_lt_mul_of_pos_left e2 hg0
      exact mul_neg_of_pos_of_neg hθQp (by linarith)
    · intro y hy
      have h1 : Real.log (G1 + G0) / theta M < y - s := by linarith [hy.1]
      have ht : Real.log (G1 + G0) < theta M * (y - s) := by
        rw [div_lt_iff₀ hθ] at h1; linarith
      have hyy : y = s + theta M * (y - s) / theta M := by rw [mul_div_cancel_left₀ _ hθ0]; ring
      rw [dd4, hyy, ev6]
      have e1 : G1 + G0 < Real.exp (theta M * (y - s)) := by
        rw [← Real.exp_log hg0]; exact Real.exp_lt_exp.2 ht
      have e2 : Real.exp (-(theta M * (y - s))) < G1 - G0 := by
        rw [← hginv, Real.exp_neg]
        exact (inv_lt_inv₀ (Real.exp_pos _) hg0).2 e1
      have p1 : 1 < (G1 - G0) * Real.exp (theta M * (y - s)) := by
        rw [← hK3, mul_comm (G1 + G0)]; exact mul_lt_mul_of_pos_left e1 hm0
      have p2 : (G1 + G0) * Real.exp (-(theta M * (y - s))) < 1 := by
        rw [← hK3]; exact mul_lt_mul_of_pos_left e2 hg0
      exact mul_pos hθQp (by linarith)
