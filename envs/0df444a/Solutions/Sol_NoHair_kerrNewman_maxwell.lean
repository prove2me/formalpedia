-- Prove2me | solution 1 for NoHair.kerrNewman_maxwell
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T06:19:53.406986+00:00
-- url     : https://prove2.me/submissions/9f4bd85d-684f-4238-b7fe-2eb3c9a9b77a

import Mathlib
import Definitions.Def_NoHair_kerrNewman
import Theorems.Thm_NoHair_kerrNewman_flat_maxwell

set_option autoImplicit false

/-!
# Kerr–Newman: curved source-free Maxwell equation, reduced to the flat one

On the open set `U = {z | 0 < ksRadius a z}` the Kerr–Schild vector `k` is null, so
`det g = -1` and `g⁻¹ = η - f k♯ k♯ᵀ` (`k♯ = η k`). The field `F = dA`, `A = H k`, satisfies the
alignment `F k♯ = λ k` (from `η(k,k) = 0` and the geodesic property `∇_{k♯} k = 0`, both checked
with explicit first derivatives of `r`). Hence `√|det g| F^{μν} = η^{μα} η^{νβ} F_{αβ}` on `U`,
and the curved Maxwell equation at `y` is the flat one, `NoHair.kerrNewman_flat_maxwell`.
-/

open scoped ContDiff Manifold BigOperators
open Set Matrix NoHair

private lemma ksRadius_eq' (a : ℝ) : ksRadius a = fun w : E4 => Real.sqrt ((w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 - a ^ 2 +
    Real.sqrt ((w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * w 3 ^ 2)) / 2) := rfl

private lemma ks_Q_pos (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    0 < (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2 +
      Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)) / 2 := by
  rw [ksRadius_eq'] at hz
  exact Real.sqrt_pos.mp hz

private lemma ks_sq (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ksRadius a z ^ 2 = (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2 +
      Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)) / 2 := by
  have h := ks_Q_pos a z hz
  rw [ksRadius_eq']
  exact Real.sq_sqrt h.le

private lemma ks_S_sq (a : ℝ) (z : E4) :
    Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2) ^ 2
      = (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2 :=
  Real.sq_sqrt (by positivity)

private lemma ks_C (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ksRadius a z ^ 4 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) * ksRadius a z ^ 2 - a ^ 2 * z 3 ^ 2 = 0 := by
  have h1 := ks_sq a z hz
  have h2 := ks_S_sq a z
  set S := Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)
  set P := z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2
  set r := ksRadius a z
  linear_combination (r ^ 2 - P / 2 + S / 2) * h1 + (1 / 4 : ℝ) * h2

private lemma ks_S_eq (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)
      = 2 * ksRadius a z ^ 2 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) := by
  have h1 := ks_sq a z hz
  linarith

private lemma ks_D_pos (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    0 < (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2 := by
  have h1 := ks_sq a z hz
  have hr2 : 0 < ksRadius a z ^ 2 := by positivity
  rcases (show (0:ℝ) ≤ (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2 by positivity).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, Real.sqrt_zero] at h1
    have hP : (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 = 0 := by nlinarith [sq_nonneg (a * z 3)]
    have hP' : z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hP
    rw [hP'] at h1
    linarith

private lemma ks_S_pos (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    0 < 2 * ksRadius a z ^ 2 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) := by
  rw [← ks_S_eq a z hz]
  exact Real.sqrt_pos.mpr (ks_D_pos a z hz)

private lemma ks_den_pos (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    0 < ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 := by positivity

private lemma ksRadius_differentiableAt (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private lemma line_apply (z v : E4) (t : ℝ) (j : Fin 4) : (z + t • v) j = z j + t * v j := by simp

private lemma hasDerivAt_line_coord (z v : E4) (j : Fin 4) :
    HasDerivAt (fun t : ℝ => z j + t * v j) (v j) 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v j)).const_add (z j)

private lemma hasDerivAt_ksRadius_line (a : ℝ) (z v : E4) (hz : 0 < ksRadius a z) :
    HasDerivAt (fun t : ℝ => ksRadius a (z + t • v))
      (ksRadius a z * (ksRadius a z ^ 2 * (z 1 * v 1 + z 2 * v 2) + (ksRadius a z ^ 2 + a ^ 2) * z 3 * v 3)
        / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)) 0 := by
  have e : (fun t : ℝ => ksRadius a (z + t • v)) = fun t : ℝ =>
      Real.sqrt (((z 1 + t * v 1) ^ 2 + (z 2 + t * v 2) ^ 2 + (z 3 + t * v 3) ^ 2 - a ^ 2 +
        Real.sqrt (((z 1 + t * v 1) ^ 2 + (z 2 + t * v 2) ^ 2 + (z 3 + t * v 3) ^ 2 - a ^ 2) ^ 2
          + 4 * a ^ 2 * (z 3 + t * v 3) ^ 2)) / 2) := by
    funext t
    rw [ksRadius_eq']
    simp only [line_apply]
  rw [e]
  have h1 := hasDerivAt_line_coord z v 1
  have h2 := hasDerivAt_line_coord z v 2
  have h3 := hasDerivAt_line_coord z v 3
  have hP := (((h1.pow 2).add (h2.pow 2)).add (h3.pow 2)).sub_const (a ^ 2)
  have hD := (hP.pow 2).add ((h3.pow 2).const_mul (4 * a ^ 2))
  have hD0 := ks_D_pos a z hz
  have hQ0 := ks_Q_pos a z hz
  have hSq := hD.sqrt (by simpa using hD0.ne')
  have hQ := (hP.add hSq).div_const 2
  have hR := hQ.sqrt (by simpa using hQ0.ne')
  convert hR using 1
  · rfl
  have hr0 : Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2 + Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)) / 2) = ksRadius a z := rfl
  simp only [zero_mul, add_zero, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat,
    show (2:ℕ) - 1 = 1 from rfl, pow_one]
  rw [hr0]
  have hSe := ks_S_eq a z hz
  have hS := ks_S_pos a z hz
  rw [← hSe] at hS
  have hC := ks_C a z hz
  have hden := ks_den_pos a z hz
  have hr1 := hz
  set S := Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)
  set r := ksRadius a z
  field_simp
  linear_combination (2*(2*a^2*r^2*(v 3)*(z 3) - a^2*(v 1)*(z 3)^2*(z 1) - a^2*(v 2)*(z 3)^2*(z 2) - a^2*(v 3)*(z 3)^3 + r^4*(v 1)*(z 1) + r^4*(v 2)*(z 2) + r^4*(v 3)*(z 3))) * hSe + (4*(a^2*(v 3)*(z 3) + r^2*(v 1)*(z 1) + r^2*(v 2)*(z 2) + r^2*(v 3)*(z 3))) * hC

private lemma fderiv_eq_of_line {g : E4 → ℝ} {z v : E4} {c : ℝ} (hg : DifferentiableAt ℝ g z)
    (h : HasDerivAt (fun t : ℝ => g (z + t • v)) c 0) : fderiv ℝ g z v = c := by
  have h1 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have h2 : HasFDerivAt g (fderiv ℝ g z) (z + (0:ℝ) • v) := by
    simpa using hg.hasFDerivAt
  exact (h2.comp_hasDerivAt (0:ℝ) h1).unique h

private lemma hasDerivAt_k1_aux {R X1 X2 : ℝ → ℝ} {dr d1 d2 : ℝ} (a : ℝ) (hR : HasDerivAt R dr 0)
    (h1 : HasDerivAt X1 d1 0) (h2 : HasDerivAt X2 d2 0) (hne : R 0 ^ 2 + a ^ 2 ≠ 0) :
    HasDerivAt (fun t => (R t * X1 t + a * X2 t) / (R t ^ 2 + a ^ 2))
      (((dr * X1 0 + R 0 * d1 + a * d2) * (R 0 ^ 2 + a ^ 2)
        - (R 0 * X1 0 + a * X2 0) * (2 * R 0 * dr)) / (R 0 ^ 2 + a ^ 2) ^ 2) 0 := by
  have := ((hR.fun_mul h1).fun_add (h2.const_mul a)).fun_div ((hR.fun_pow 2).add_const (a ^ 2)) hne
  refine this.congr_deriv ?_
  norm_num

private lemma hasDerivAt_k2_aux {R X1 X2 : ℝ → ℝ} {dr d1 d2 : ℝ} (a : ℝ) (hR : HasDerivAt R dr 0)
    (h1 : HasDerivAt X1 d1 0) (h2 : HasDerivAt X2 d2 0) (hne : R 0 ^ 2 + a ^ 2 ≠ 0) :
    HasDerivAt (fun t => (R t * X2 t - a * X1 t) / (R t ^ 2 + a ^ 2))
      (((dr * X2 0 + R 0 * d2 - a * d1) * (R 0 ^ 2 + a ^ 2)
        - (R 0 * X2 0 - a * X1 0) * (2 * R 0 * dr)) / (R 0 ^ 2 + a ^ 2) ^ 2) 0 := by
  have := ((hR.fun_mul h2).fun_sub (h1.const_mul a)).fun_div ((hR.fun_pow 2).add_const (a ^ 2)) hne
  refine this.congr_deriv ?_
  norm_num

private lemma hasDerivAt_k3_aux {R X3 : ℝ → ℝ} {dr d3 : ℝ} (hR : HasDerivAt R dr 0)
    (h3 : HasDerivAt X3 d3 0) (hne : R 0 ≠ 0) :
    HasDerivAt (fun t => X3 t / R t) ((d3 * R 0 - X3 0 * dr) / R 0 ^ 2) 0 :=
  h3.fun_div hR hne

private lemma ksNull_zero (a : ℝ) (w : E4) : ksNull a w 0 = 1 := rfl
private lemma ksNull_one (a : ℝ) (w : E4) :
    ksNull a w 1 = (ksRadius a w * w 1 + a * w 2) / (ksRadius a w ^ 2 + a ^ 2) := rfl
private lemma ksNull_two (a : ℝ) (w : E4) :
    ksNull a w 2 = (ksRadius a w * w 2 - a * w 1) / (ksRadius a w ^ 2 + a ^ 2) := rfl
private lemma ksNull_three (a : ℝ) (w : E4) : ksNull a w 3 = w 3 / ksRadius a w := rfl

/-- directional derivative of `r` -/
private noncomputable def drf (a : ℝ) (z v : E4) : ℝ :=
  ksRadius a z * (ksRadius a z ^ 2 * (z 1 * v 1 + z 2 * v 2) + (ksRadius a z ^ 2 + a ^ 2) * z 3 * v 3)
    / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)

private noncomputable def dk1f (a : ℝ) (z v : E4) : ℝ :=
  ((drf a z v * z 1 + ksRadius a z * v 1 + a * v 2) * (ksRadius a z ^ 2 + a ^ 2)
    - (ksRadius a z * z 1 + a * z 2) * (2 * ksRadius a z * drf a z v)) / (ksRadius a z ^ 2 + a ^ 2) ^ 2

private noncomputable def dk2f (a : ℝ) (z v : E4) : ℝ :=
  ((drf a z v * z 2 + ksRadius a z * v 2 - a * v 1) * (ksRadius a z ^ 2 + a ^ 2)
    - (ksRadius a z * z 2 - a * z 1) * (2 * ksRadius a z * drf a z v)) / (ksRadius a z ^ 2 + a ^ 2) ^ 2

private noncomputable def dk3f (a : ℝ) (z v : E4) : ℝ :=
  (v 3 * ksRadius a z - z 3 * drf a z v) / ksRadius a z ^ 2

private lemma ksNull_differentiableAt (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    DifferentiableAt ℝ (fun w => ksNull a w i) z := by
  have hr := ksRadius_differentiableAt a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' : ksRadius a z ≠ 0 := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · show DifferentiableAt ℝ (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · show DifferentiableAt ℝ (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

private lemma fderiv_k1 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (v : E4) :
    fderiv ℝ (fun w => ksNull a w 1) z v = dk1f a z v := by
  apply fderiv_eq_of_line (ksNull_differentiableAt a z hz 1)
  have hR := hasDerivAt_ksRadius_line a z v hz
  have := hasDerivAt_k1_aux a hR (hasDerivAt_line_coord z v 1) (hasDerivAt_line_coord z v 2)
    (by simp only [zero_smul, add_zero]; positivity)
  have e : (fun t : ℝ => ksNull a (z + t • v) 1) = fun t => (ksRadius a (z + t • v) * (z 1 + t * v 1)
      + a * (z 2 + t * v 2)) / (ksRadius a (z + t • v) ^ 2 + a ^ 2) := by
    funext t; rw [ksNull_one, line_apply, line_apply]
  rw [e]
  refine this.congr_deriv ?_
  simp only [zero_smul, add_zero, zero_mul]
  rfl

private lemma fderiv_k2 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (v : E4) :
    fderiv ℝ (fun w => ksNull a w 2) z v = dk2f a z v := by
  apply fderiv_eq_of_line (ksNull_differentiableAt a z hz 2)
  have hR := hasDerivAt_ksRadius_line a z v hz
  have := hasDerivAt_k2_aux a hR (hasDerivAt_line_coord z v 1) (hasDerivAt_line_coord z v 2)
    (by simp only [zero_smul, add_zero]; positivity)
  have e : (fun t : ℝ => ksNull a (z + t • v) 2) = fun t => (ksRadius a (z + t • v) * (z 2 + t * v 2)
      - a * (z 1 + t * v 1)) / (ksRadius a (z + t • v) ^ 2 + a ^ 2) := by
    funext t; rw [ksNull_two, line_apply, line_apply]
  rw [e]
  refine this.congr_deriv ?_
  simp only [zero_smul, add_zero, zero_mul]
  rfl

private lemma fderiv_k3 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (v : E4) :
    fderiv ℝ (fun w => ksNull a w 3) z v = dk3f a z v := by
  apply fderiv_eq_of_line (ksNull_differentiableAt a z hz 3)
  have hR := hasDerivAt_ksRadius_line a z v hz
  have := hasDerivAt_k3_aux hR (hasDerivAt_line_coord z v 3)
    (by simp only [zero_smul, add_zero]; exact hz.ne')
  have e : (fun t : ℝ => ksNull a (z + t • v) 3) = fun t => (z 3 + t * v 3) / ksRadius a (z + t • v) := by
    funext t; rw [ksNull_three, line_apply]
  rw [e]
  refine this.congr_deriv ?_
  simp only [zero_smul, add_zero, zero_mul]
  rfl

private lemma fderiv_k0 (a : ℝ) (z : E4) : fderiv ℝ (fun w => ksNull a w 0) z = 0 := by
  simp only [ksNull_zero]
  exact fderiv_const_apply _

private lemma ks_null (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    -(ksNull a z 0) ^ 2 + ksNull a z 1 ^ 2 + ksNull a z 2 ^ 2 + ksNull a z 3 ^ 2 = 0 := by
  rw [ksNull_zero, ksNull_one, ksNull_two, ksNull_three]
  have hC := ks_C a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hr := hz.ne'
  set r := ksRadius a z
  field_simp
  linear_combination (-a^2 - r^2) * hC

private lemma ks_drf_V (a : ℝ) (z v : E4) (hz : 0 < ksRadius a z) (h1 : v 1 = ksNull a z 1)
    (h2 : v 2 = ksNull a z 2) (h3 : v 3 = ksNull a z 3) : drf a z v = 1 := by
  rw [drf, h1, h2, h3, ksNull_one, ksNull_two, ksNull_three]
  have hC := ks_C a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hden := (ks_den_pos a z hz).ne'
  have hr := hz.ne'
  set r := ksRadius a z
  field_simp
  linear_combination (-r^2) * hC

private lemma ks_dnull (a : ℝ) (z v : E4) (hz : 0 < ksRadius a z) :
    ksNull a z 1 * dk1f a z v + ksNull a z 2 * dk2f a z v + ksNull a z 3 * dk3f a z v = 0 := by
  rw [dk1f, dk2f, dk3f, drf, ksNull_one, ksNull_two, ksNull_three]
  have hC := ks_C a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hden := (ks_den_pos a z hz).ne'
  have hr := hz.ne'
  set r := ksRadius a z
  field_simp
  linear_combination (r^2*(a^2 + r^2)*(a^2*(v 3)*(z 3) + r^2*(v 1)*(z 1) + r^2*(v 2)*(z 2) + r^2*(v 3)*(z 3))) * hC

private lemma ks_geo1 (a : ℝ) (z v : E4) (hz : 0 < ksRadius a z) (h1 : v 1 = ksNull a z 1)
    (h2 : v 2 = ksNull a z 2) (h3 : v 3 = ksNull a z 3) : dk1f a z v = 0 := by
  rw [dk1f, ks_drf_V a z v hz h1 h2 h3, h1, h2, ksNull_one, ksNull_two]
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma ks_geo2 (a : ℝ) (z v : E4) (hz : 0 < ksRadius a z) (h1 : v 1 = ksNull a z 1)
    (h2 : v 2 = ksNull a z 2) (h3 : v 3 = ksNull a z 3) : dk2f a z v = 0 := by
  rw [dk2f, ks_drf_V a z v hz h1 h2 h3, h1, h2, ksNull_one, ksNull_two]
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma ks_geo3 (a : ℝ) (z v : E4) (hz : 0 < ksRadius a z) (h1 : v 1 = ksNull a z 1)
    (h2 : v 2 = ksNull a z 2) (h3 : v 3 = ksNull a z 3) : dk3f a z v = 0 := by
  rw [dk3f, ks_drf_V a z v hz h1 h2 h3, h3, ksNull_three]
  have hr := hz.ne'
  field_simp
  ring

private lemma sum_coordBasis_apply (c : Fin 4 → ℝ) (j : Fin 4) :
    (∑ ν, c ν • coordBasis ν : E4) j = c j := by
  fin_cases j <;> simp [coordBasis, Fin.sum_univ_four]

private lemma fderiv_sum_coordBasis (g : E4 → ℝ) (z : E4) (c : Fin 4 → ℝ) :
    ∑ ν, c ν * coordPartial g ν z = fderiv ℝ g z (∑ ν, c ν • coordBasis ν) := by
  simp [coordPartial, map_sum, map_smul]

private noncomputable def Hf (a e : ℝ) (w : E4) : ℝ := e * ksRadius a w ^ 3 / (ksRadius a w ^ 4 + a ^ 2 * w 3 ^ 2)

private lemma Hf_differentiableAt (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (Hf a e) z := by
  have hr := ksRadius_differentiableAt a z hz
  have hden := (ks_den_pos a z hz).ne'
  unfold Hf
  fun_prop (disch := assumption)

private lemma potential_eq (a e : ℝ) (β : Fin 4) :
    (fun w => kerrNewmanPotential a e w β) = Hf a e * (fun w => ksNull a w β) := by
  funext w; rfl

private lemma coordPartial_potential (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (α β : Fin 4) :
    coordPartial (fun w => kerrNewmanPotential a e w β) α z
      = coordPartial (Hf a e) α z * ksNull a z β
        + Hf a e z * coordPartial (fun w => ksNull a w β) α z := by
  rw [coordPartial, potential_eq,
    fderiv_mul (Hf_differentiableAt a e z hz) (ksNull_differentiableAt a z hz β)]
  simp only [coordPartial, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private lemma field_eq (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (μ ν : Fin 4) :
    kerrNewmanField a e z μ ν
      = (coordPartial (Hf a e) μ z * ksNull a z ν + Hf a e z * coordPartial (fun w => ksNull a w ν) μ z)
        - (coordPartial (Hf a e) ν z * ksNull a z μ
          + Hf a e z * coordPartial (fun w => ksNull a w μ) ν z) := by
  show coordPartial (fun w => kerrNewmanPotential a e w ν) μ z
    - coordPartial (fun w => kerrNewmanPotential a e w μ) ν z = _
  rw [coordPartial_potential a e z hz, coordPartial_potential a e z hz]

private lemma align_alg (dH : Fin 4 → ℝ) (H : ℝ) (k ks : Fin 4 → ℝ) (pk : Fin 4 → Fin 4 → ℝ)
    (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ μ ν, F μ ν = (dH μ * k ν + H * pk ν μ) - (dH ν * k μ + H * pk μ ν))
    (hN : ∑ ν, k ν * ks ν = 0) (hI : ∀ μ, ∑ ν, pk ν μ * ks ν = 0)
    (hG : ∀ μ, ∑ ν, pk μ ν * ks ν = 0) (μ : Fin 4) :
    ∑ ν, F μ ν * ks ν = (-∑ ν, dH ν * ks ν) * k μ := by
  simp only [hF]
  have h1 := hI μ
  have h2 := hG μ
  simp only [Fin.sum_univ_four] at *
  linear_combination dH μ * hN + H * h1 - H * h2

private lemma ks_hN (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ∑ ν, ksNull a z ν * ![-ksNull a z 0, ksNull a z 1, ksNull a z 2, ksNull a z 3] ν = 0 := by
  have := ks_null a z hz
  simp only [Fin.sum_univ_four]
  simp
  linear_combination this

private lemma ks_hI (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (μ : Fin 4) :
    ∑ ν, coordPartial (fun w => ksNull a w ν) μ z
      * ![-ksNull a z 0, ksNull a z 1, ksNull a z 2, ksNull a z 3] ν = 0 := by
  have := ks_dnull a z (coordBasis μ) hz
  simp only [Fin.sum_univ_four, coordPartial]
  simp [fderiv_k0, fderiv_k1 a z hz, fderiv_k2 a z hz, fderiv_k3 a z hz]
  linear_combination this

private lemma ks_hG (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (μ : Fin 4) :
    ∑ ν, coordPartial (fun w => ksNull a w μ) ν z
      * ![-ksNull a z 0, ksNull a z 1, ksNull a z 2, ksNull a z 3] ν = 0 := by
  set ks : Fin 4 → ℝ := ![-ksNull a z 0, ksNull a z 1, ksNull a z 2, ksNull a z 3] with hks
  have e : ∑ ν, coordPartial (fun w => ksNull a w μ) ν z * ks ν
      = ∑ ν, ks ν * coordPartial (fun w => ksNull a w μ) ν z := by
    simp only [mul_comm]
  rw [e, fderiv_sum_coordBasis]
  have h1 : (∑ ν, ks ν • coordBasis ν : E4) 1 = ksNull a z 1 := by
    rw [sum_coordBasis_apply]; simp [hks]
  have h2 : (∑ ν, ks ν • coordBasis ν : E4) 2 = ksNull a z 2 := by
    rw [sum_coordBasis_apply]; simp [hks]
  have h3 : (∑ ν, ks ν • coordBasis ν : E4) 3 = ksNull a z 3 := by
    rw [sum_coordBasis_apply]; simp [hks]
  fin_cases μ
  · simp [fderiv_k0]
  · exact (fderiv_k1 a z hz _).trans (ks_geo1 a z _ hz h1 h2 h3)
  · exact (fderiv_k2 a z hz _).trans (ks_geo2 a z _ hz h1 h2 h3)
  · exact (fderiv_k3 a z hz _).trans (ks_geo3 a z _ hz h1 h2 h3)

private lemma det_KS (f : ℝ) (k : Fin 4 → ℝ) (hnull : -(k 0) ^ 2 + k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 = 0) :
    Matrix.det (Matrix.of fun μ ν => minkowski μ ν + f * k μ * k ν) = -1 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, minkowski, Fin.succAbove, Matrix.submatrix]
  linear_combination (-f) * hnull

private lemma mul_inv_KS (f : ℝ) (k : Fin 4 → ℝ) (hnull : -(k 0) ^ 2 + k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 = 0) :
    (Matrix.of fun μ ν => minkowski μ ν + f * k μ * k ν) *
      (Matrix.of fun μ ν => minkowski μ ν - f * ![-k 0, k 1, k 2, k 3] μ * ![-k 0, k 1, k 2, k 3] ν) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four]
  linear_combination (norm := skip) (-f ^ 2 * k i * ![-k 0, k 1, k 2, k 3] j) * hnull
  fin_cases i <;> fin_cases j <;> simp [minkowski] <;> ring

private lemma raise_KS (f lam : ℝ) (k : Fin 4 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hnull : -(k 0) ^ 2 + k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 = 0)
    (hanti : ∀ α β, F β α = - F α β)
    (halign : ∀ α, ∑ β, F α β * ![-k 0, k 1, k 2, k 3] β = lam * k α) (μ ν : Fin 4) :
    ∑ α, ∑ β, (minkowski μ α - f * ![-k 0, k 1, k 2, k 3] μ * ![-k 0, k 1, k 2, k 3] α) *
      (minkowski ν β - f * ![-k 0, k 1, k 2, k 3] ν * ![-k 0, k 1, k 2, k 3] β) * F α β
      = ∑ α, ∑ β, minkowski μ α * minkowski ν β * F α β := by
  set ks : Fin 4 → ℝ := ![-k 0, k 1, k 2, k 3] with hks
  have h0 := halign 0
  have h1 := halign 1
  have h2 := halign 2
  have h3 := halign 3
  have hm := halign μ
  have hn := halign ν
  have a0 := hanti 0 ν
  have a1 := hanti 1 ν
  have a2 := hanti 2 ν
  have a3 := hanti 3 ν
  simp only [Fin.sum_univ_four] at *
  linear_combination (norm := skip) (-f * ks ν * minkowski μ μ) * hm + (f * ks μ * minkowski ν ν) * hn
    - f * ks μ * minkowski ν ν * (ks 0 * a0 + ks 1 * a1 + ks 2 * a2 + ks 3 * a3)
    + f ^ 2 * ks μ * ks ν * (ks 0 * h0 + ks 1 * h1 + ks 2 * h2 + ks 3 * h3)
    + f ^ 2 * ks μ * ks ν * lam * hnull
  fin_cases μ <;> fin_cases ν <;> simp [minkowski, hks] <;> ring

private lemma field_anti (a e : ℝ) (z : E4) (α β : Fin 4) :
    kerrNewmanField a e z β α = - kerrNewmanField a e z α β := by
  simp only [kerrNewmanField]; ring

private lemma star_eq (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (μ ν : Fin 4) :
    Real.sqrt |(kerrNewmanMetric m a e z).det|
        * raiseBoth (kerrNewmanMetric m a e) (kerrNewmanField a e) z μ ν
      = ∑ α, ∑ β, minkowski μ α * minkowski ν β * kerrNewmanField a e z α β := by
  have hG : kerrNewmanMetric m a e z
      = Matrix.of fun μ ν => minkowski μ ν + ksProfile m a e z * ksNull a z μ * ksNull a z ν := rfl
  have hnull := ks_null a z hz
  have hdet : (kerrNewmanMetric m a e z).det = -1 := by
    rw [hG]; exact det_KS _ _ hnull
  have hinv : (kerrNewmanMetric m a e z)⁻¹ = Matrix.of fun μ ν => minkowski μ ν
      - ksProfile m a e z * ![-ksNull a z 0, ksNull a z 1, ksNull a z 2, ksNull a z 3] μ
        * ![-ksNull a z 0, ksNull a z 1, ksNull a z 2, ksNull a z 3] ν := by
    rw [hG]; exact Matrix.inv_eq_right_inv (mul_inv_KS _ _ hnull)
  rw [hdet, abs_neg, abs_one, Real.sqrt_one, one_mul]
  simp only [raiseBoth, invMetric, hinv, Matrix.of_apply]
  refine raise_KS _ (-∑ ν, coordPartial (Hf a e) ν z
    * ![-ksNull a z 0, ksNull a z 1, ksNull a z 2, ksNull a z 3] ν) _ _ hnull (field_anti a e z) ?_ μ ν
  intro α
  exact align_alg _ _ _ _ _ _ (field_eq a e z hz) (ks_hN a z hz) (ks_hI a z hz) (ks_hG a z hz) α

theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ ν, ∑ μ, coordPartial
      (fun z => Real.sqrt |(kerrNewmanMetric m a e z).det|
        * raiseBoth (kerrNewmanMetric m a e) (kerrNewmanField a e) z μ ν) μ y = 0 := by
  intro ν
  have hU : IsOpen {z : E4 | 0 < ksRadius a z} := isOpen_lt continuous_const (continuous_ksRadius a)
  have key : ∀ μ, coordPartial
      (fun z => Real.sqrt |(kerrNewmanMetric m a e z).det|
        * raiseBoth (kerrNewmanMetric m a e) (kerrNewmanField a e) z μ ν) μ y
      = coordPartial
      (fun z => ∑ α, ∑ β, minkowski μ α * minkowski ν β * kerrNewmanField a e z α β) μ y := by
    intro μ
    unfold coordPartial
    rw [Filter.EventuallyEq.fderiv_eq]
    filter_upwards [hU.mem_nhds hy] with z hz
    exact star_eq m a e z hz μ ν
  rw [Finset.sum_congr rfl (fun μ _ => key μ)]
  exact kerrNewman_flat_maxwell a e y hy ν
