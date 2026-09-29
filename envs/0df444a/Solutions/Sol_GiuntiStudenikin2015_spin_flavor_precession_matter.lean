-- Prove2me | solution 1 for GiuntiStudenikin2015.spin_flavor_precession_matter
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T05:22:08.591211+00:00
-- url     : https://prove2.me/submissions/de1c4625-e198-4d1c-a66c-cd68121a6b62

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem gs15_normSq_hasDerivAt {u : ℝ → ℂ} {u' : ℂ} {x : ℝ} (hu : HasDerivAt u u' x) :
    HasDerivAt (fun t => Complex.normSq (u t)) (2 * ((u x).re * u'.re + (u x).im * u'.im)) x := by
  have hre : HasDerivAt (fun t => (u t).re) u'.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hu
  have him : HasDerivAt (fun t => (u t).im) u'.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hu
  have h2 : HasDerivAt (fun t => (u t).re * (u t).re + (u t).im * (u t).im)
      (u'.re * (u x).re + (u x).re * u'.re + (u'.im * (u x).im + (u x).im * u'.im)) x :=
    (hre.mul hre).add (him.mul him)
  have e : (fun t => Complex.normSq (u t)) =
      fun t => (u t).re * (u t).re + (u t).im * (u t).im := by
    funext t; exact Complex.normSq_apply _
  rw [e]
  convert h2 using 1
  ring

theorem gs15_ode_uniq (p q r : ℝ → ℝ) (ψ φ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ x, HasDerivAt ψ ![-(Complex.I * ((p x : ℂ) * ψ x 0 + (q x : ℂ) * ψ x 1)),
      -(Complex.I * ((q x : ℂ) * ψ x 0 + (r x : ℂ) * ψ x 1))] x)
    (hφ : ∀ x, HasDerivAt φ ![-(Complex.I * ((p x : ℂ) * φ x 0 + (q x : ℂ) * φ x 1)),
      -(Complex.I * ((q x : ℂ) * φ x 0 + (r x : ℂ) * φ x 1))] x)
    (h0 : ψ 0 = φ 0) (x : ℝ) : ψ x = φ x := by
  have hd0 : ∀ y, HasDerivAt (fun t => ψ t 0 - φ t 0)
      (-(Complex.I * ((p y : ℂ) * (ψ y 0 - φ y 0) + (q y : ℂ) * (ψ y 1 - φ y 1)))) y := by
    intro y
    have h := ((hasDerivAt_pi.mp (hψ y)) 0).sub ((hasDerivAt_pi.mp (hφ y)) 0)
    have e : (-(Complex.I * ((p y : ℂ) * (ψ y 0 - φ y 0) + (q y : ℂ) * (ψ y 1 - φ y 1)))) =
        -(Complex.I * ((p y : ℂ) * ψ y 0 + (q y : ℂ) * ψ y 1)) -
          -(Complex.I * ((p y : ℂ) * φ y 0 + (q y : ℂ) * φ y 1)) := by ring
    rw [e]
    exact h
  have hd1 : ∀ y, HasDerivAt (fun t => ψ t 1 - φ t 1)
      (-(Complex.I * ((q y : ℂ) * (ψ y 0 - φ y 0) + (r y : ℂ) * (ψ y 1 - φ y 1)))) y := by
    intro y
    have h := ((hasDerivAt_pi.mp (hψ y)) 1).sub ((hasDerivAt_pi.mp (hφ y)) 1)
    have e : (-(Complex.I * ((q y : ℂ) * (ψ y 0 - φ y 0) + (r y : ℂ) * (ψ y 1 - φ y 1)))) =
        -(Complex.I * ((q y : ℂ) * ψ y 0 + (r y : ℂ) * ψ y 1)) -
          -(Complex.I * ((q y : ℂ) * φ y 0 + (r y : ℂ) * φ y 1)) := by ring
    rw [e]
    exact h
  have hN : ∀ y, HasDerivAt
      (fun t => Complex.normSq (ψ t 0 - φ t 0) + Complex.normSq (ψ t 1 - φ t 1)) 0 y := by
    intro y
    have h : HasDerivAt
        (fun t => Complex.normSq (ψ t 0 - φ t 0) + Complex.normSq (ψ t 1 - φ t 1)) _ y :=
      (gs15_normSq_hasDerivAt (hd0 y)).add (gs15_normSq_hasDerivAt (hd1 y))
    convert h using 1
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun y => (hN y).differentiableAt)
    (fun y => (hN y).deriv) x 0
  have e0 : ψ 0 0 - φ 0 0 = 0 := by rw [h0]; ring
  have e1 : ψ 0 1 - φ 0 1 = 0 := by rw [h0]; ring
  simp only [e0, e1, map_zero, add_zero] at hconst
  have n0 := Complex.normSq_nonneg (ψ x 0 - φ x 0)
  have n1 := Complex.normSq_nonneg (ψ x 1 - φ x 1)
  have z0 : Complex.normSq (ψ x 0 - φ x 0) = 0 := by linarith
  have z1 : Complex.normSq (ψ x 1 - φ x 1) = 0 := by linarith
  rw [Complex.normSq_eq_zero, sub_eq_zero] at z0 z1
  funext i
  fin_cases i
  · exact z0
  · exact z1

theorem gs15_const_sol (p q r : ℝ) (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ y, HasDerivAt ψ ![-(Complex.I * ((p : ℂ) * ψ y 0 + (q : ℂ) * ψ y 1)),
      -(Complex.I * ((q : ℂ) * ψ y 0 + (r : ℂ) * ψ y 1))] y)
    (h0 : ψ 0 = ![1, 0]) (x : ℝ) :
    Complex.normSq (ψ x 1) =
      (q / Real.sqrt (((p - r) / 2) ^ 2 + q ^ 2)) ^ 2 *
        Real.sin (Real.sqrt (((p - r) / 2) ^ 2 + q ^ 2) * x) ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (p - r) / 2 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (p + r) / 2 := ⟨_, rfl⟩
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : ℝ, Ω = Real.sqrt (a ^ 2 + q ^ 2) := ⟨_, rfl⟩
  rw [← ha, ← hΩdef]
  have hΩsq : Ω ^ 2 = a ^ 2 + q ^ 2 := by rw [hΩdef]; exact Real.sq_sqrt (by positivity)
  by_cases hΩ : Ω = 0
  · have hq : q = 0 := by
      have h1 : a ^ 2 + q ^ 2 = 0 := by rw [← hΩsq, hΩ]; ring
      have h2 : q ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg q]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    subst hq
    set φ : ℝ → Fin 2 → ℂ := fun y =>
      ![Complex.exp (-(Complex.I * ((p * y : ℝ) : ℂ))), 0] with hφdef
    have hφ : ∀ y, HasDerivAt φ ![-(Complex.I * ((p : ℂ) * φ y 0 + ((0 : ℝ) : ℂ) * φ y 1)),
        -(Complex.I * (((0 : ℝ) : ℂ) * φ y 0 + (r : ℂ) * φ y 1))] y := by
      intro y
      refine hasDerivAt_pi.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · have h : HasDerivAt (fun t => φ t 0)
            (Complex.exp (-(Complex.I * ((p * y : ℝ) : ℂ))) * -(Complex.I * ((p * 1 : ℝ) : ℂ))) y :=
          (((hasDerivAt_id y).const_mul p).ofReal_comp.const_mul Complex.I).neg.cexp
        refine h.congr_deriv ?_
        simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_zero, Complex.ofReal_one]
        ring
      · have h : HasDerivAt (fun t => φ t 1) 0 y := hasDerivAt_const y (0 : ℂ)
        refine h.congr_deriv ?_
        simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Complex.ofReal_zero]
        ring
    have heq := gs15_ode_uniq (fun _ => p) (fun _ => (0 : ℝ)) (fun _ => r) ψ φ hψ hφ
      (by rw [h0]; funext i; fin_cases i <;> simp [φ]) x
    rw [heq]
    simp [φ]
  · obtain ⟨s, hs⟩ : ∃ s : ℝ, s = a / Ω := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = q / Ω := ⟨_, rfl⟩
    have hsΩ : Ω * s = a := by rw [hs]; field_simp
    have htΩ : Ω * t = q := by rw [ht]; field_simp
    have hst : s ^ 2 + t ^ 2 = 1 := by
      rw [hs, ht, div_pow, div_pow, ← add_div, ← hΩsq, div_self (pow_ne_zero 2 hΩ)]
    have h1 : (p : ℂ) = (m : ℂ) + (Ω : ℂ) * (s : ℂ) := by
      have : p = m + Ω * s := by rw [hsΩ, hm, ha]; ring
      exact_mod_cast this
    have h2 : (q : ℂ) = (Ω : ℂ) * (t : ℂ) := by exact_mod_cast htΩ.symm
    have h3 : (s : ℂ) ^ 2 + (t : ℂ) ^ 2 = 1 := by exact_mod_cast hst
    have h4 : (r : ℂ) = (m : ℂ) - (Ω : ℂ) * (s : ℂ) := by
      have : r = m - Ω * s := by rw [hsΩ, hm, ha]; ring
      exact_mod_cast this
    set φ : ℝ → Fin 2 → ℂ := fun y =>
      ![Complex.exp (-(Complex.I * ((m * y : ℝ) : ℂ))) *
          (((Real.cos (Ω * y)) : ℝ) - Complex.I * (s : ℂ) * ((Real.sin (Ω * y) : ℝ) : ℂ)),
        Complex.exp (-(Complex.I * ((m * y : ℝ) : ℂ))) *
          (-(Complex.I * (t : ℂ) * ((Real.sin (Ω * y) : ℝ) : ℂ)))] with hφdef
    have hφ : ∀ y, HasDerivAt φ ![-(Complex.I * ((p : ℂ) * φ y 0 + (q : ℂ) * φ y 1)),
        -(Complex.I * ((q : ℂ) * φ y 0 + (r : ℂ) * φ y 1))] y := by
      intro y
      have hE := (((hasDerivAt_id y).const_mul m).ofReal_comp.const_mul Complex.I).neg.cexp
      have hC := (((hasDerivAt_id y).const_mul Ω).cos).ofReal_comp
      have hS := (((hasDerivAt_id y).const_mul Ω).sin).ofReal_comp
      refine hasDerivAt_pi.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · have h := hE.mul (hC.sub (hS.const_mul (Complex.I * (s : ℂ))))
        refine h.congr_deriv ?_
        simp only [φ, id, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Pi.sub_apply, Pi.neg_apply, Pi.mul_apply,
          Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one]
        linear_combination
          (Complex.I * Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) *
              ((Real.cos (Ω * y) : ℝ) : ℂ) +
            Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) * ((Real.sin (Ω * y) : ℝ) : ℂ) *
              (s : ℂ)) * h1 +
          Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) * ((Real.sin (Ω * y) : ℝ) : ℂ) *
              (t : ℂ) * h2 +
          Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) * ((Real.sin (Ω * y) : ℝ) : ℂ) *
              (Ω : ℂ) * h3 +
          Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) * ((Real.sin (Ω * y) : ℝ) : ℂ) *
              ((m : ℂ) * (s : ℂ) - (p : ℂ) * (s : ℂ) - (q : ℂ) * (t : ℂ)) * Complex.I_sq
      · have h := hE.mul ((hS.const_mul (Complex.I * (t : ℂ))).neg)
        refine h.congr_deriv ?_
        simp only [φ, id, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Pi.sub_apply, Pi.neg_apply, Pi.mul_apply,
          Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one]
        linear_combination
          (Complex.I * Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) *
              ((Real.cos (Ω * y) : ℝ) : ℂ) +
            Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) * ((Real.sin (Ω * y) : ℝ) : ℂ) *
              (s : ℂ)) * h2 +
          Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) * ((Real.sin (Ω * y) : ℝ) : ℂ) *
              (t : ℂ) * h4 +
          Complex.exp (-(Complex.I * ((m : ℂ) * (y : ℂ)))) * ((Real.sin (Ω * y) : ℝ) : ℂ) *
              ((m : ℂ) * (t : ℂ) - (q : ℂ) * (s : ℂ) - (r : ℂ) * (t : ℂ)) * Complex.I_sq
    have heq := gs15_ode_uniq (fun _ => p) (fun _ => q) (fun _ => r) ψ φ hψ hφ
      (by rw [h0]; funext i; fin_cases i <;> simp [φ]) x
    have hE1 : Complex.normSq (Complex.exp (-(Complex.I * ((m * x : ℝ) : ℂ)))) = 1 := by
      rw [Complex.normSq_eq_norm_sq,
        show -(Complex.I * ((m * x : ℝ) : ℂ)) = ((-(m * x) : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
      norm_num
    rw [heq]
    show Complex.normSq (Complex.exp (-(Complex.I * ((m * x : ℝ) : ℂ))) *
          (-(Complex.I * (t : ℂ) * ((Real.sin (Ω * x) : ℝ) : ℂ)))) = _
    rw [Complex.normSq_mul, hE1, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_I, Complex.normSq_ofReal, Complex.normSq_ofReal, ← ht]
    ring
theorem gs15_sfh_mulVec (V μ B : ℝ) (v : Fin 2 → ℂ) :
    -(Complex.I • (GiuntiStudenikin2015.spinFlavorHamiltonian V μ B).mulVec v) =
      ![-(Complex.I * ((V : ℂ) * v 0 + ((μ * B : ℝ) : ℂ) * v 1)),
        -(Complex.I * (((μ * B : ℝ) : ℂ) * v 0 + ((0 : ℝ) : ℂ) * v 1))] := by
  ext i
  fin_cases i <;>
    simp [GiuntiStudenikin2015.spinFlavorHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

open GiuntiStudenikin2015 in
theorem solution (V μ B : ℝ) (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ x : ℝ, HasDerivAt ψ (-(Complex.I • (spinFlavorHamiltonian V μ B).mulVec (ψ x))) x)
    (h0 : ψ 0 = ![1, 0]) (x : ℝ) :
    Complex.normSq (ψ x 1) =
      (2 * μ * B / spinFlavorEnergySplitting V μ B) ^ 2 *
        Real.sin (spinFlavorEnergySplitting V μ B * x / 2) ^ 2 := by
  have hψ' : ∀ y, HasDerivAt ψ ![-(Complex.I * ((V : ℂ) * ψ y 0 + ((μ * B : ℝ) : ℂ) * ψ y 1)),
      -(Complex.I * (((μ * B : ℝ) : ℂ) * ψ y 0 + ((0 : ℝ) : ℂ) * ψ y 1))] y := by
    intro y
    have h := hψ y
    rw [gs15_sfh_mulVec] at h
    exact h
  rw [gs15_const_sol V (μ * B) 0 ψ hψ' h0 x]
  have hsq : Real.sqrt (((V - 0) / 2) ^ 2 + (μ * B) ^ 2) =
      spinFlavorEnergySplitting V μ B / 2 := by
    unfold spinFlavorEnergySplitting
    rw [show ((V - 0) / 2) ^ 2 + (μ * B) ^ 2 = (V ^ 2 + (2 * μ * B) ^ 2) / 2 ^ 2 by ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num)]
  rw [hsq, show spinFlavorEnergySplitting V μ B / 2 * x = spinFlavorEnergySplitting V μ B * x / 2 by
    ring]
  congr 1
  ring
