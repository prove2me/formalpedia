-- Prove2me | solution 1 for GiuntiStudenikin2015.spin_precession_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T05:18:22.600396+00:00
-- url     : https://prove2.me/submissions/eb503deb-2ff1-4090-978d-79ca3f52a506

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

theorem gs15_sfh_mulVec (V μ B : ℝ) (v : Fin 2 → ℂ) :
    -(Complex.I • (GiuntiStudenikin2015.spinFlavorHamiltonian V μ B).mulVec v) =
      ![-(Complex.I * ((V : ℂ) * v 0 + ((μ * B : ℝ) : ℂ) * v 1)),
        -(Complex.I * (((μ * B : ℝ) : ℂ) * v 0 + ((0 : ℝ) : ℂ) * v 1))] := by
  ext i
  fin_cases i <;>
    simp [GiuntiStudenikin2015.spinFlavorHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

open GiuntiStudenikin2015 in
theorem solution (μ : ℝ) (B : ℝ → ℝ) (hB : Continuous B)
    (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ x : ℝ, HasDerivAt ψ (-(Complex.I • (spinFlavorHamiltonian 0 μ (B x)).mulVec (ψ x))) x)
    (h0 : ψ 0 = ![1, 0]) (x : ℝ) :
    Complex.normSq (ψ x 1) = Real.sin (∫ t in (0 : ℝ)..x, μ * B t) ^ 2 := by
  set Φ : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, μ * B t with hΦdef
  have hΦ : ∀ y, HasDerivAt Φ (μ * B y) y := fun y =>
    ((continuous_const.mul hB).integral_hasStrictDerivAt 0 y).hasDerivAt
  set φ : ℝ → Fin 2 → ℂ := fun y =>
    ![((Real.cos (Φ y) : ℝ) : ℂ), -(Complex.I * ((Real.sin (Φ y) : ℝ) : ℂ))] with hφdef
  have hψ' : ∀ y, HasDerivAt ψ
      ![-(Complex.I * ((((fun _ => (0 : ℝ)) y) : ℂ) * ψ y 0 + (((fun t => μ * B t) y) : ℂ) * ψ y 1)),
        -(Complex.I * ((((fun t => μ * B t) y) : ℂ) * ψ y 0 + (((fun _ => (0 : ℝ)) y) : ℂ) * ψ y 1))] y := by
    intro y
    have h := hψ y
    rw [gs15_sfh_mulVec] at h
    simpa using h
  have hφ' : ∀ y, HasDerivAt φ
      ![-(Complex.I * ((((fun _ => (0 : ℝ)) y) : ℂ) * φ y 0 + (((fun t => μ * B t) y) : ℂ) * φ y 1)),
        -(Complex.I * ((((fun t => μ * B t) y) : ℂ) * φ y 0 + (((fun _ => (0 : ℝ)) y) : ℂ) * φ y 1))] y := by
    intro y
    refine hasDerivAt_pi.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · have h : HasDerivAt (fun t => φ t 0) ((-(Real.sin (Φ y)) * (μ * B y) : ℝ) : ℂ) y :=
        ((hΦ y).cos).ofReal_comp
      refine h.congr_deriv ?_
      simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_zero]
      linear_combination (-(μ : ℂ) * (B y : ℂ) * ((Real.sin (Φ y) : ℝ) : ℂ)) * Complex.I_sq
    · have h : HasDerivAt (fun t => φ t 1)
          (-(Complex.I * ((Real.cos (Φ y) * (μ * B y) : ℝ) : ℂ))) y :=
        (((hΦ y).sin).ofReal_comp.const_mul Complex.I).neg
      refine h.congr_deriv ?_
      simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_zero]
      ring
  have heq := gs15_ode_uniq (fun _ => (0 : ℝ)) (fun t => μ * B t) (fun _ => (0 : ℝ)) ψ φ hψ' hφ'
    (by rw [h0]; funext i; fin_cases i <;> simp [φ, Φ]) x
  rw [heq]
  show Complex.normSq (-(Complex.I * ((Real.sin (Φ x) : ℝ) : ℂ))) = Real.sin (Φ x) ^ 2
  rw [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]
  ring
