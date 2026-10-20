-- Prove2me | solution 1 for ImpulseGames.LinearGame.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T15:14:25.754385+00:00
-- url     : https://prove2.me/submissions/6154f6d5-0bf6-433f-85d6-0c6d912e5aa8

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
theorem prop42 (M : Model) (hM : M.Standing) (hc : 0 < M.c)
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

namespace Pcdb7

open ImpulseGames.LinearGame Real P5f0a

lemma quad_factor {a b c t1 t2 t : ℝ} (h1 : a * t1 ^ 2 + b * t1 + c = 0)
    (h2 : a * t2 ^ 2 + b * t2 + c = 0) (hne : t1 ≠ t2) :
    a * t ^ 2 + b * t + c = a * (t - t1) * (t - t2) := by
  have hb : b + a * t1 + a * t2 = 0 := by
    have h : (t1 - t2) * (a * (t1 + t2) + b) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · linear_combination h
  have hc : c - a * t1 * t2 = 0 := by linear_combination h1 - t1 * hb
  linear_combination t * hb + hc

lemma pos_of_exp_mul {E X P : ℝ} (hE : 0 < E) (h : E * X = P) (hP : 0 < P) : 0 < X := by
  by_contra hX
  push Not at hX
  have := mul_nonpos_of_nonneg_of_nonpos hE.le hX
  linarith

lemma neg_of_exp_mul {E X P : ℝ} (hE : 0 < E) (h : E * X = P) (hP : P < 0) : X < 0 := by
  by_contra hX
  push Not at hX
  have := mul_nonneg hE.le hX
  linarith

section S
variable (M : Model) (ξ s : ℝ)

noncomputable def Wt2 (y : ℝ) : ℝ := Vt2 M ξ s (-y)
noncomputable def Ph2 (y : ℝ) : ℝ := phiTwo M ξ s (-y)
noncomputable def dPh2 (y : ℝ) : ℝ := -d1Two M ξ s (-y)

lemma e_mul_d1One (y : ℝ) : exp (theta M * y) * (d1One M ξ s y - M.lam) =
    theta M * A M ξ s 1 1 * exp (theta M * y) ^ 2 + (1 / M.ρ - M.lam) * exp (theta M * y)
      + -(theta M * A M ξ s 1 2) := by
  have h : exp (theta M * y) * exp (-(theta M * y)) = 1 := by rw [← exp_add]; simp
  unfold d1One
  linear_combination (-(theta M * A M ξ s 1 2)) * h

lemma e_mul_d1Two (y : ℝ) : exp (theta M * y) * (d1Two M ξ s y + M.lam) =
    theta M * A M ξ s 2 1 * exp (theta M * y) ^ 2 + (M.lam - 1 / M.ρ) * exp (theta M * y)
      + -(theta M * A M ξ s 2 2) := by
  have h : exp (theta M * y) * exp (-(theta M * y)) = 1 := by rw [← exp_add]; simp
  unfold d1Two
  linear_combination (-(theta M * A M ξ s 2 2)) * h

lemma d1One_sign (hθ : 0 < theta M) {p q : ℝ} (hpq : p < q) (hp : d1One M ξ s p = M.lam)
    (hq : d1One M ξ s q = M.lam) (y : ℝ) :
    exp (theta M * y) * (d1One M ξ s y - M.lam) =
      theta M * A M ξ s 1 1 * (exp (theta M * y) - exp (theta M * p)) *
        (exp (theta M * y) - exp (theta M * q)) := by
  have h1 := e_mul_d1One M ξ s p
  have h2 := e_mul_d1One M ξ s q
  rw [hp, sub_self, mul_zero] at h1
  rw [hq, sub_self, mul_zero] at h2
  rw [e_mul_d1One]
  exact quad_factor h1.symm h2.symm (ne_of_lt (exp_lt_exp.2 (mul_lt_mul_of_pos_left hpq hθ)))

lemma d1Two_sign (hθ : 0 < theta M) {p q : ℝ} (hpq : p < q) (hp : d1Two M ξ s p = -M.lam)
    (hq : d1Two M ξ s q = -M.lam) (y : ℝ) :
    exp (theta M * y) * (d1Two M ξ s y + M.lam) =
      theta M * A M ξ s 2 1 * (exp (theta M * y) - exp (theta M * p)) *
        (exp (theta M * y) - exp (theta M * q)) := by
  have h1 := e_mul_d1Two M ξ s p
  have h2 := e_mul_d1Two M ξ s q
  rw [hp, neg_add_cancel, mul_zero] at h1
  rw [hq, neg_add_cancel, mul_zero] at h2
  rw [e_mul_d1Two]
  exact quad_factor h1.symm h2.symm (ne_of_lt (exp_lt_exp.2 (mul_lt_mul_of_pos_left hpq hθ)))

end S

lemma abstract1 (V φ φ' : ℝ → ℝ) (c ct lam lamt a p b q : ℝ)
    (hV : ∀ y, V y = if y ≤ a then φ p - c - lam * (p - y) else if y < b then φ y
      else φ q + ct + lamt * (y - q))
    (hd : ∀ y, HasDerivAt φ (φ' y) y)
    (hpos : ∀ y ∈ Set.Ioo a p, lam < φ' y) (hneg : ∀ y ∈ Set.Ioo p b, φ' y < lam)
    (hc1 : φ a = φ p - c - lam * (p - a)) (hc2 : φ b = φ q + ct + lamt * (b - q))
    (hc : 0 < c) (hll : lamt ≤ lam) (hap : a < p) (hpb : p < b) :
    (∀ x : ℝ, 0 ≤ max (p - x) 0 ∧ ∀ δ : ℝ, 0 ≤ δ →
      V (x + δ) - c - lam * |δ| ≤ V (x + max (p - x) 0) - c - lam * |max (p - x) 0| ∧
      ((lamt < lam ∨ x < b) → V (x + δ) - c - lam * |δ| =
        V (x + max (p - x) 0) - c - lam * |max (p - x) 0| → δ = max (p - x) 0)) ∧
    (∀ x : ℝ, sSup ((fun δ => V (x + δ) - c - lam * |δ|) '' Set.Ici 0) =
      V (x + max (p - x) 0) - c - lam * |max (p - x) 0|) ∧
    (∀ x : ℝ, (V (x + max (p - x) 0) - c - lam * |max (p - x) 0| - V x = 0 ↔ x ≤ a) ∧
      (V (x + max (p - x) 0) - c - lam * |max (p - x) 0| - V x < 0 ↔ a < x)) := by
  have GLf : ∀ y, y ≤ a → V y - lam * y = φ p - lam * p - c := by
    intro y hy; rw [hV, if_pos hy]; ring
  have GM : ∀ y, a ≤ y → y ≤ b → V y - lam * y = φ y - lam * y := by
    intro y h1 h2
    rcases eq_or_lt_of_le h1 with h1 | h1
    · rw [← h1, hV, if_pos le_rfl]; linarith [hc1]
    rcases eq_or_lt_of_le h2 with h2 | h2
    · rw [h2, hV, if_neg (not_le.2 (hap.trans hpb)), if_neg (lt_irrefl b)]; linarith [hc2]
    · rw [hV, if_neg (not_le.2 h1), if_pos h2]
  have GR : ∀ y, b ≤ y → V y - lam * y = (φ b - lam * b) + (lamt - lam) * (y - b) := by
    intro y hy
    rw [hV, if_neg (not_le.2 (by linarith : a < y)), if_neg (not_lt.2 hy), hc2]; ring
  have hg : ∀ y, HasDerivAt (fun y => φ y - lam * y) (φ' y - lam) y := fun y =>
    ((hd y).sub ((hasDerivAt_id' y).const_mul lam)).congr_deriv (by ring)
  have smono : StrictMonoOn (fun y => φ y - lam * y) (Set.Icc a p) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a p)
      (fun y _ => (hg y).continuousAt.continuousWithinAt) ?_
    intro y hy; rw [interior_Icc] at hy; rw [(hg y).deriv]; linarith [hpos y hy]
  have santi : StrictAntiOn (fun y => φ y - lam * y) (Set.Icc p b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc p b)
      (fun y _ => (hg y).continuousAt.continuousWithinAt) ?_
    intro y hy; rw [interior_Icc] at hy; rw [(hg y).deriv]; linarith [hneg y hy]
  have GP : V p - lam * p = φ p - lam * p := GM p hap.le hpb.le
  have K1 : ∀ y, y ≠ p → V y - lam * y < φ p - lam * p := by
    intro y hy
    rcases le_or_gt y a with h | h
    · rw [GLf y h]; linarith
    rcases lt_or_gt_of_ne hy with h' | h'
    · rw [GM y h.le (by linarith)]
      have e : φ y - lam * y < φ p - lam * p := smono ⟨h.le, h'.le⟩ ⟨hap.le, le_rfl⟩ h'
      exact e
    rcases le_or_gt y b with h'' | h''
    · rw [GM y h.le h'']
      have e : φ y - lam * y < φ p - lam * p := santi ⟨le_rfl, hpb.le⟩ ⟨h'.le, h''⟩ h'
      exact e
    · rw [GR y h''.le]
      have e : φ b - lam * b < φ p - lam * p := santi ⟨le_rfl, hpb.le⟩ ⟨hpb.le, le_rfl⟩ hpb
      have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hll) (sub_nonneg.2 h''.le)
      linarith
  have K2 : ∀ x y, p ≤ x → x ≤ y → V y - lam * y ≤ V x - lam * x ∧
      ((lamt < lam ∨ x < b) → x < y → V y - lam * y < V x - lam * x) := by
    intro x y hpx hxy
    rcases le_or_gt x b with hxb | hxb
    · rw [GM x (hap.le.trans hpx) hxb]
      rcases le_or_gt y b with hyb | hyb
      · rw [GM y (hap.le.trans (hpx.trans hxy)) hyb]
        have e1 : φ y - lam * y ≤ φ x - lam * x :=
          santi.antitoneOn ⟨hpx, hxb⟩ ⟨hpx.trans hxy, hyb⟩ hxy
        refine ⟨e1, fun _ h => ?_⟩
        have e2 : φ y - lam * y < φ x - lam * x := santi ⟨hpx, hxb⟩ ⟨hpx.trans hxy, hyb⟩ h
        exact e2
      · rw [GR y hyb.le]
        have hb : φ b - lam * b ≤ φ x - lam * x := santi.antitoneOn ⟨hpx, hxb⟩ ⟨hpb.le, le_rfl⟩ hxb
        have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hll) (sub_nonneg.2 hyb.le)
        refine ⟨by linarith, fun h _ => ?_⟩
        rcases h with h | h
        · have := mul_neg_of_neg_of_pos (sub_neg.2 h) (sub_pos.2 hyb)
          linarith
        · have e3 : φ b - lam * b < φ x - lam * x := santi ⟨hpx, hxb⟩ ⟨hpb.le, le_rfl⟩ h
          linarith
    · rw [GR x hxb.le, GR y (hxb.le.trans hxy)]
      have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hll) (sub_nonneg.2 hxy)
      refine ⟨by linarith, fun h hlt => ?_⟩
      rcases h with h | h
      · have := mul_neg_of_neg_of_pos (sub_neg.2 h) (sub_pos.2 hlt)
        linarith
      · linarith
  have K3 : ∀ x, a < x → x ≤ p → φ p - lam * p - c < V x - lam * x := by
    intro x h1 h2
    rw [GM x h1.le (h2.trans hpb.le)]
    have e : φ a - lam * a < φ x - lam * x := smono ⟨le_rfl, hap.le⟩ ⟨h1.le, h2⟩ h1
    linarith [hc1]
  have key : ∀ x δ, 0 ≤ δ → V (x + δ) - c - lam * |δ| = (V (x + δ) - lam * (x + δ)) + lam * x - c := by
    intro x δ h; rw [abs_of_nonneg h]; ring
  have P1 : ∀ x : ℝ, 0 ≤ max (p - x) 0 ∧ ∀ δ : ℝ, 0 ≤ δ →
      V (x + δ) - c - lam * |δ| ≤ V (x + max (p - x) 0) - c - lam * |max (p - x) 0| ∧
      ((lamt < lam ∨ x < b) → V (x + δ) - c - lam * |δ| =
        V (x + max (p - x) 0) - c - lam * |max (p - x) 0| → δ = max (p - x) 0) := by
    intro x
    refine ⟨le_max_right _ _, fun δ hδ => ?_⟩
    rw [key x δ hδ, key x (max (p - x) 0) (le_max_right _ _)]
    rcases le_or_gt x p with hxp | hxp
    · rw [max_eq_left (by linarith : 0 ≤ p - x), show x + (p - x) = p by ring, GP]
      by_cases hy : x + δ = p
      · rw [hy, GP]; exact ⟨le_rfl, fun _ _ => by linarith⟩
      · have := K1 (x + δ) hy
        exact ⟨by linarith, fun _ h => by exfalso; linarith⟩
    · rw [max_eq_right (by linarith : p - x ≤ 0), add_zero]
      have := K2 x (x + δ) hxp.le (by linarith)
      refine ⟨by linarith [this.1], fun h heq => ?_⟩
      by_contra hne
      have hδ' : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hne)
      have := this.2 h (by linarith)
      linarith
  have P2 : ∀ x : ℝ, sSup ((fun δ => V (x + δ) - c - lam * |δ|) '' Set.Ici 0) =
      V (x + max (p - x) 0) - c - lam * |max (p - x) 0| := by
    intro x
    apply IsGreatest.csSup_eq
    refine ⟨⟨max (p - x) 0, Set.mem_Ici.2 (le_max_right _ _), rfl⟩, ?_⟩
    rintro _ ⟨δ, hδ, rfl⟩
    exact ((P1 x).2 δ hδ).1
  have P3 : ∀ x : ℝ, (V (x + max (p - x) 0) - c - lam * |max (p - x) 0| - V x = 0 ↔ x ≤ a) ∧
      (V (x + max (p - x) 0) - c - lam * |max (p - x) 0| - V x < 0 ↔ a < x) := by
    intro x
    rw [key x (max (p - x) 0) (le_max_right _ _)]
    rcases le_or_gt x p with hxp | hxp
    · rw [max_eq_left (by linarith : 0 ≤ p - x), show x + (p - x) = p by ring, GP]
      rcases le_or_gt x a with hxa | hxa
      · have := GLf x hxa
        constructor <;> constructor <;> intro h <;> linarith
      · have := K3 x hxa hxp
        constructor <;> constructor <;> intro h <;> linarith
    · rw [max_eq_right (by linarith : p - x ≤ 0), add_zero]
      constructor <;> constructor <;> intro h <;> linarith
  exact ⟨P1, P2, P3⟩

end Pcdb7

open ImpulseGames.LinearGame in
theorem solution (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 (eta M)) (hFξ : F M ξ = 0) (s : ℝ) :
    -- (4.23): δ₁(x) is a maximiser over Z₁ = [0, ∞[, the unique one unless λ = λ̃ and x ≥ x̄₂
    (∀ x : ℝ, 0 ≤ delta1 M ξ s x ∧
      ∀ δ : ℝ, 0 ≤ δ →
        Vt1 M ξ s (x + δ) - M.c - M.lam * |δ| ≤
          Vt1 M ξ s (x + delta1 M ξ s x) - M.c - M.lam * |delta1 M ξ s x| ∧
        ((M.lamt < M.lam ∨ x < xbar M ξ s 2) →
          Vt1 M ξ s (x + δ) - M.c - M.lam * |δ| =
          Vt1 M ξ s (x + delta1 M ξ s x) - M.c - M.lam * |delta1 M ξ s x| →
            δ = delta1 M ξ s x)) ∧
    -- (4.23): δ₂(x) is a maximiser over Z₂ = ]−∞, 0], the unique one unless λ = λ̃ and x ≤ x̄₁
    (∀ x : ℝ, delta2 M ξ s x ≤ 0 ∧
      ∀ δ : ℝ, δ ≤ 0 →
        Vt2 M ξ s (x + δ) - M.c - M.lam * |δ| ≤
          Vt2 M ξ s (x + delta2 M ξ s x) - M.c - M.lam * |delta2 M ξ s x| ∧
        ((M.lamt < M.lam ∨ xbar M ξ s 1 < x) →
          Vt2 M ξ s (x + δ) - M.c - M.lam * |δ| =
          Vt2 M ξ s (x + delta2 M ξ s x) - M.c - M.lam * |delta2 M ξ s x| →
            δ = delta2 M ξ s x)) ∧
    -- (4.24), player 1
    (∀ x : ℝ, M1op M (Vt1 M ξ s) x - Vt1 M ξ s x ≤ 0) ∧
    {x : ℝ | M1op M (Vt1 M ξ s) x - Vt1 M ξ s x < 0} = Set.Ioi (xbar M ξ s 1) ∧
    {x : ℝ | M1op M (Vt1 M ξ s) x - Vt1 M ξ s x = 0} = Set.Iic (xbar M ξ s 1) ∧
    -- (4.24), player 2
    (∀ x : ℝ, M2op M (Vt2 M ξ s) x - Vt2 M ξ s x ≤ 0) ∧
    {x : ℝ | M2op M (Vt2 M ξ s) x - Vt2 M ξ s x < 0} = Set.Iio (xbar M ξ s 2) ∧
    {x : ℝ | M2op M (Vt2 M ξ s) x - Vt2 M ξ s x = 0} = Set.Ici (xbar M ξ s 2) := by
  obtain ⟨⟨o1, o2⟩, ⟨o3, o4⟩, ⟨h8a, -⟩, h8b, h8c, h8d, ⟨h9a, -⟩, h9b, h9c, h9d, -⟩ :=
    prop42 M hM hc ξ hξ hFξ s
  rw [P5f0a.deriv_phiOne] at h8a h8b
  rw [P5f0a.deriv_phiTwo] at h9a h9b
  have hθ : 0 < theta M := Real.sqrt_pos.2 (by have := hM.σ_pos; have := hM.ρ_pos; positivity)
  have hη : 0 < eta M := div_pos hM.one_sub_lam_mul_ρ_pos hM.ρ_pos
  have hΓ := P5f0a.Gam_pos M ξ hM hc hξ.1
  have hll := hM.lamt_le_lam
  have hab : xbar M ξ s 1 < xbar M ξ s 2 := o1.trans o2
  have hK : ∀ j : ℕ, 0 < Real.exp ((-1 : ℝ) ^ j * theta M * s) *
      Real.sqrt (eta M ^ 2 - ξ ^ 2) / (2 * theta M) := by
    intro j
    have : 0 < eta M ^ 2 - ξ ^ 2 := by nlinarith [hξ.1, hξ.2]
    exact div_pos (mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 this)) (by linarith)
  have hs1 := Real.sqrt_pos.2 (show (0:ℝ) < Gam M ξ + 1 by linarith)
  have hs2 := Real.sqrt_nonneg (Gam M ξ)
  have hs3 := Real.sqrt_lt_sqrt hΓ.le (show Gam M ξ < Gam M ξ + 1 by linarith)
  have hA11 : A M ξ s 1 1 < 0 := by
    unfold A
    refine mul_neg_of_pos_of_neg (hK 1) ?_
    have e : (-1 : ℝ) ^ (1 + 1 + 1) = -1 := by norm_num
    rw [e]; linarith
  have hA21 : 0 < A M ξ s 2 1 := by
    unfold A
    refine mul_pos (hK 1) ?_
    have e : (-1 : ℝ) ^ (2 + 1 + 1) = 1 := by norm_num
    rw [e]; linarith
  have pos1 : ∀ y ∈ Set.Ioo (xbar M ξ s 1) (xstar M ξ s 1), M.lam < P5f0a.d1One M ξ s y := by
    rintro y ⟨hy1, hy2⟩
    have hf := Pcdb7.d1One_sign M ξ s hθ o1 h8b h8a y
    have e1 := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hy1 hθ)
    have e2 := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hy2 hθ)
    have hP := mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hθ hA11)
      (sub_pos.2 e1)) (sub_neg.2 e2)
    have := Pcdb7.pos_of_exp_mul (Real.exp_pos _) hf hP
    linarith
  have neg1 : ∀ y ∈ Set.Ioo (xstar M ξ s 1) (xbar M ξ s 2), P5f0a.d1One M ξ s y < M.lam := by
    rintro y ⟨hy1, hy2⟩
    have hf := Pcdb7.d1One_sign M ξ s hθ o1 h8b h8a y
    have e1 := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (o1.trans hy1) hθ)
    have e2 := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hy1 hθ)
    have hP := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hθ hA11)
      (sub_pos.2 e1)) (sub_pos.2 e2)
    have := Pcdb7.neg_of_exp_mul (Real.exp_pos _) hf hP
    linarith
  have pos2 : ∀ y ∈ Set.Ioo (-xbar M ξ s 2) (-xstar M ξ s 2), M.lam < Pcdb7.dPh2 M ξ s y := by
    rintro y ⟨hy1, hy2⟩
    show M.lam < -P5f0a.d1Two M ξ s (-y)
    have hf := Pcdb7.d1Two_sign M ξ s hθ o4 h9a h9b (-y)
    have e1 := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (by linarith : xstar M ξ s 2 < -y) hθ)
    have e2 := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (by linarith : -y < xbar M ξ s 2) hθ)
    have hP := mul_neg_of_pos_of_neg (mul_pos (mul_pos hθ hA21) (sub_pos.2 e1)) (sub_neg.2 e2)
    have := Pcdb7.neg_of_exp_mul (Real.exp_pos _) hf hP
    linarith
  have neg2 : ∀ y ∈ Set.Ioo (-xstar M ξ s 2) (-xbar M ξ s 1), Pcdb7.dPh2 M ξ s y < M.lam := by
    rintro y ⟨hy1, hy2⟩
    show -P5f0a.d1Two M ξ s (-y) < M.lam
    have hf := Pcdb7.d1Two_sign M ξ s hθ o4 h9a h9b (-y)
    have e1 := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (by linarith : -y < xstar M ξ s 2) hθ)
    have e2 := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (by linarith : -y < xbar M ξ s 2) hθ)
    have hP := mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (mul_pos hθ hA21) (sub_neg.2 e1))
      (sub_neg.2 e2)
    have := Pcdb7.pos_of_exp_mul (Real.exp_pos _) hf hP
    linarith
  have hV2 : ∀ y, Pcdb7.Wt2 M ξ s y = if y ≤ -xbar M ξ s 2 then
      Pcdb7.Ph2 M ξ s (-xstar M ξ s 2) - M.c - M.lam * (-xstar M ξ s 2 - y)
      else if y < -xbar M ξ s 1 then Pcdb7.Ph2 M ξ s y
      else Pcdb7.Ph2 M ξ s (-xstar M ξ s 1) + M.ct + M.lamt * (y - -xstar M ξ s 1) := by
    intro y
    unfold Pcdb7.Wt2 Pcdb7.Ph2 Vt2
    simp only [neg_neg]
    split_ifs <;> first | (exfalso; linarith) | ring
  have hd2 : ∀ y, HasDerivAt (Pcdb7.Ph2 M ξ s) (Pcdb7.dPh2 M ξ s y) y := by
    intro y
    show HasDerivAt (fun y => phiTwo M ξ s (-y)) (-P5f0a.d1Two M ξ s (-y)) y
    exact ((P5f0a.hasDerivAt_phiTwo M ξ s (-y)).comp y (hasDerivAt_neg y)).congr_deriv (by ring)
  have hc1' : Pcdb7.Ph2 M ξ s (-xbar M ξ s 2) =
      Pcdb7.Ph2 M ξ s (-xstar M ξ s 2) - M.c - M.lam * (-xstar M ξ s 2 - -xbar M ξ s 2) := by
    unfold Pcdb7.Ph2; simp only [neg_neg]; rw [h9d]; ring
  have hc2' : Pcdb7.Ph2 M ξ s (-xbar M ξ s 1) =
      Pcdb7.Ph2 M ξ s (-xstar M ξ s 1) + M.ct + M.lamt * (-xbar M ξ s 1 - -xstar M ξ s 1) := by
    unfold Pcdb7.Ph2; simp only [neg_neg]; rw [h9c]; ring
  obtain ⟨A1, A2, A3⟩ := Pcdb7.abstract1 (Vt1 M ξ s) (phiOne M ξ s) (P5f0a.d1One M ξ s)
    M.c M.ct M.lam M.lamt (xbar M ξ s 1) (xstar M ξ s 1) (xbar M ξ s 2) (xstar M ξ s 2)
    (fun y => rfl) (P5f0a.hasDerivAt_phiOne M ξ s) pos1 neg1 h8c h8d hc hll o1 o2
  obtain ⟨B1, B2, B3⟩ := Pcdb7.abstract1 (Pcdb7.Wt2 M ξ s) (Pcdb7.Ph2 M ξ s) (Pcdb7.dPh2 M ξ s)
    M.c M.ct M.lam M.lamt (-xbar M ξ s 2) (-xstar M ξ s 2) (-xbar M ξ s 1) (-xstar M ξ s 1)
    hV2 hd2 pos2 neg2 hc1' hc2' hc hll (neg_lt_neg o4) (neg_lt_neg o3)
  have hdel2 : ∀ x, delta2 M ξ s x = -(max (-xstar M ξ s 2 - -x) 0) := by
    intro x; unfold delta2
    rcases le_total (xstar M ξ s 2 - x) 0 with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  have hS2 : ∀ x, M2op M (Vt2 M ξ s) x =
      sSup ((fun δ => Pcdb7.Wt2 M ξ s (-x + δ) - M.c - M.lam * |δ|) '' Set.Ici 0) := by
    intro x; unfold M2op; congr 1; ext z; constructor
    · rintro ⟨δ, hδ, rfl⟩
      refine ⟨-δ, Set.mem_Ici.2 (neg_nonneg.2 (Set.mem_Iic.1 hδ)), ?_⟩
      show Vt2 M ξ s (-(-x + -δ)) - M.c - M.lam * |-δ| = Vt2 M ξ s (x + δ) - M.c - M.lam * |δ|
      rw [abs_neg, show -(-x + -δ) = x + δ by ring]
    · rintro ⟨δ, hδ, rfl⟩
      refine ⟨-δ, Set.mem_Iic.2 (neg_nonpos.2 (Set.mem_Ici.1 hδ)), ?_⟩
      show Vt2 M ξ s (x + -δ) - M.c - M.lam * |-δ| = Vt2 M ξ s (-(-x + δ)) - M.c - M.lam * |δ|
      rw [abs_neg, show -(-x + δ) = x + -δ by ring]
  have hW : ∀ x, Pcdb7.Wt2 M ξ s (-x) = Vt2 M ξ s x := fun x => by
    unfold Pcdb7.Wt2; rw [neg_neg]
  refine ⟨A1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨-, hB⟩ := B1 (-x)
    rw [hdel2 x]
    refine ⟨by linarith [le_max_right (-xstar M ξ s 2 - -x) 0], fun δ hδ => ?_⟩
    have hB' := hB (-δ) (by linarith)
    have e1 : Vt2 M ξ s (x + δ) = Pcdb7.Wt2 M ξ s (-x + -δ) := by
      unfold Pcdb7.Wt2; congr 1; ring
    have e2 : Vt2 M ξ s (x + -max (-xstar M ξ s 2 - -x) 0) =
        Pcdb7.Wt2 M ξ s (-x + max (-xstar M ξ s 2 - -x) 0) := by
      unfold Pcdb7.Wt2; congr 1; ring
    rw [e1, e2, abs_neg, ← abs_neg δ]
    refine ⟨hB'.1, fun h heq => ?_⟩
    have := hB'.2 (h.imp_right (fun h' => by linarith)) heq
    linarith
  · intro x
    unfold M1op; rw [A2 x]
    rcases le_or_gt x (xbar M ξ s 1) with h | h
    · exact ((A3 x).1.2 h).le
    · exact ((A3 x).2.2 h).le
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
    unfold M1op; rw [A2 x]; exact (A3 x).2
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    unfold M1op; rw [A2 x]; exact (A3 x).1
  · intro x
    rw [hS2 x, B2 (-x), ← hW x]
    rcases le_or_gt (-x) (-xbar M ξ s 2) with h | h
    · exact ((B3 (-x)).1.2 h).le
    · exact ((B3 (-x)).2.2 h).le
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Iio]
    rw [hS2 x, B2 (-x), ← hW x, (B3 (-x)).2]
    exact neg_lt_neg_iff
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    rw [hS2 x, B2 (-x), ← hW x, (B3 (-x)).1]
    exact neg_le_neg_iff
