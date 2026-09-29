-- Prove2me | solution 1 for GravitationalConstant.surface_gravity_from_newton_law
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:08:59.786321+00:00
-- url     : https://prove2.me/submissions/4531a17b-2c53-4cb0-b031-c463fa49ff55

import Definitions.Def_GravitationalConstantBasic

open GravitationalConstant

theorem W2p_GravitationalConstant_key (G M r P : ℝ) (horb : IsCircularOrbit G M r P) :
    P ^ 2 * (G * M) = 4 * Real.pi ^ 2 * r ^ 3 := by
  obtain ⟨hr, hP, h⟩ := horb
  have e : (2 * Real.pi / P) ^ 2 * r = 4 * Real.pi ^ 2 * r / P ^ 2 := by
    rw [div_pow]; ring
  rw [e, div_eq_div_iff (by positivity) (by positivity)] at h
  linear_combination -h

theorem W2p_GravitationalConstant_gravitational_constant_si_eq_cgs
    (metre kilogram second centimetre gram dyne : ℝ)
    (hcm : metre = 100 * centimetre) (hg : kilogram = 1000 * gram)
    (hdyn : dyne = gram * centimetre / second ^ 2)
    (hcm0 : centimetre ≠ 0) (hg0 : gram ≠ 0) (hs0 : second ≠ 0) :
    gravitationalConstantSI * (metre ^ 3 / (kilogram * second ^ 2)) =
      6.67430e-8 * (dyne * centimetre ^ 2 / gram ^ 2) := by
  subst hcm hg hdyn
  unfold gravitationalConstantSI
  rw [show (6.67430e-11 : ℝ) = 667430 / 10 ^ 16 by norm_num,
    show (6.67430e-8 : ℝ) = 667430 / 10 ^ 13 by norm_num]
  field_simp <;> ring

theorem W2p_GravitationalConstant_einstein_constant_determines_newton_constant
    (G c : ℝ) (hc : c ≠ 0) :
    G = einsteinConstant G c * c ^ 4 / (8 * Real.pi) := by
  unfold einsteinConstant
  have := Real.pi_pos.ne'
  field_simp <;> ring

theorem W2p_GravitationalConstant_circular_orbit_period_sq
    (G M r P : ℝ) (hG : 0 < G) (hM : 0 < M) (horb : IsCircularOrbit G M r P) :
    P ^ 2 = 4 * Real.pi ^ 2 * r ^ 3 / (G * M) := by
  rw [eq_div_iff (by positivity)]
  exact W2p_GravitationalConstant_key G M r P horb

theorem W2p_GravitationalConstant_grazing_orbit_period_mean_density
    (G M R P : ℝ) (hG : 0 < G) (hM : 0 < M) (horb : IsCircularOrbit G M R P) :
    P ^ 2 = 3 * Real.pi / (G * meanDensity M R) := by
  have hR := horb.1
  rw [W2p_GravitationalConstant_circular_orbit_period_sq G M R P hG hM horb]
  unfold meanDensity ballVolume
  have := Real.pi_pos.ne'
  field_simp <;> ring

theorem W2p_GravitationalConstant_keplers_third_law_circular
    (G M r₁ P₁ r₂ P₂ : ℝ) (hG : 0 < G) (hM : 0 < M)
    (h₁ : IsCircularOrbit G M r₁ P₁) (h₂ : IsCircularOrbit G M r₂ P₂) :
    P₁ ^ 2 / r₁ ^ 3 = P₂ ^ 2 / r₂ ^ 3 := by
  have hr₁ := h₁.1
  have hr₂ := h₂.1
  rw [W2p_GravitationalConstant_circular_orbit_period_sq G M r₁ P₁ hG hM h₁,
    W2p_GravitationalConstant_circular_orbit_period_sq G M r₂ P₂ hG hM h₂]
  field_simp <;> ring

theorem W2p_GravitationalConstant_surface_gravity_mean_density
    (G M R : ℝ) (hR : 0 < R) :
    surfaceGravity G M R = 4 / 3 * Real.pi * G * meanDensity M R * R := by
  unfold surfaceGravity meanDensity ballVolume
  have := Real.pi_pos.ne'
  field_simp <;> ring

theorem W2p_GravitationalConstant_surface_gravity_from_newton_law
    (G M m R : ℝ) (hm : m ≠ 0) :
    newtonForce G M m R / m = surfaceGravity G M R := by
  unfold newtonForce surfaceGravity
  rw [div_right_comm, mul_div_cancel_right₀ _ hm]

theorem W2p_GravitationalConstant_newton_constant_from_orbital_volume
    (G M r P : ℝ) (hG : 0 < G) (hM : 0 < M) (horb : IsCircularOrbit G M r P) :
    G = 3 * Real.pi * ballVolume r / (P ^ 2 * M) := by
  have hP := horb.2.1
  have key := W2p_GravitationalConstant_key G M r P horb
  rw [eq_div_iff (by positivity)]
  unfold ballVolume
  linear_combination key

theorem solution
    (G M m R : ℝ) (hm : m ≠ 0) :
    newtonForce G M m R / m = surfaceGravity G M R := by
  apply W2p_GravitationalConstant_surface_gravity_from_newton_law <;> assumption
