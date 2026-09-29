-- Prove2me | solution 1 for HooftMonopole.omega_unitary
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:56:18.008577+00:00
-- url     : https://prove2.me/submissions/c9869989-de45-409c-9229-f21f209f22ee

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real
open HooftMonopole

theorem W4b_HooftMonopole_fin2_eq {a b c d a' b' c' d' : ℂ} (h1 : a = a') (h2 : b = b')
    (h3 : c = c') (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h1, h2, h3, h4]

theorem W4b_HooftMonopole_omega_form (c s φ : ℝ) :
    (c : ℂ) • !![Complex.exp (Complex.I * φ), 0; 0, Complex.exp (-(Complex.I * φ))]
      + (s : ℂ) • !![0, Complex.I; Complex.I, 0] =
      !![(c : ℂ) * Complex.exp (Complex.I * φ), (s : ℂ) * Complex.I;
        (s : ℂ) * Complex.I, (c : ℂ) * Complex.exp (-(Complex.I * φ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem W4b_HooftMonopole_conjT (c s φ : ℝ) :
    (!![(c : ℂ) * Complex.exp (Complex.I * φ), (s : ℂ) * Complex.I;
        (s : ℂ) * Complex.I, (c : ℂ) * Complex.exp (-(Complex.I * φ))]).conjTranspose =
      !![(c : ℂ) * Complex.exp (-(Complex.I * φ)), -((s : ℂ) * Complex.I);
        -((s : ℂ) * Complex.I), (c : ℂ) * Complex.exp (Complex.I * φ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.ext_iff, Complex.exp_re, Complex.exp_im]

theorem W4b_HooftMonopole_unit_aux (C S E E' J : ℂ) (h1 : E * E' = 1) (hCS : C ^ 2 + S ^ 2 = 1)
    (hJ : J * J = -1) :
    !![C * E, S * J; S * J, C * E'] * !![C * E', -(S * J); -(S * J), C * E] = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  refine W4b_HooftMonopole_fin2_eq ?_ ?_ ?_ ?_
  · linear_combination C ^ 2 * h1 + hCS - S ^ 2 * hJ
  · ring
  · ring
  · linear_combination C ^ 2 * h1 + hCS - S ^ 2 * hJ

theorem W4b_HooftMonopole_adj_aux (C S E E' J cφ sφ : ℂ) (h1 : E * E' = 1) (hJ : J * J = -1)
    (hE : E = cφ + J * sφ) (hE' : E' = cφ - J * sφ) :
    !![C * E, S * J; S * J, C * E'] * !![1, 0; 0, -1] *
        !![C * E', -(S * J); -(S * J), C * E] =
      !![C ^ 2 - S ^ 2, 2 * S * C * sφ - 2 * S * C * cφ * J;
        2 * S * C * sφ + 2 * S * C * cφ * J, -(C ^ 2 - S ^ 2)] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine W4b_HooftMonopole_fin2_eq ?_ ?_ ?_ ?_
  · linear_combination C ^ 2 * h1 + S ^ 2 * hJ
  · linear_combination (-2 * C * S * J) * hE + (-2 * C * S * sφ) * hJ
  · linear_combination (2 * C * S * J) * hE' + (-2 * C * S * sφ) * hJ
  · linear_combination (-S ^ 2) * hJ + (-C ^ 2) * h1

theorem W4b_HooftMonopole_rhs_form (A B D : ℝ) :
    (A : ℂ) • pauli 0 + (B : ℂ) • pauli 1 + (D : ℂ) • pauli 2 =
      !![(D : ℂ), (A : ℂ) - (B : ℂ) * Complex.I; (A : ℂ) + (B : ℂ) * Complex.I, -(D : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring

theorem solution (θ φ : ℝ) :
    omegaMatrix θ φ * (omegaMatrix θ φ).conjTranspose = 1 := by
  have hΩ : omegaMatrix θ φ =
      !![((Real.cos (θ / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * φ),
          ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I;
        ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I,
          ((Real.cos (θ / 2) : ℝ) : ℂ) * Complex.exp (-(Complex.I * φ))] :=
    W4b_HooftMonopole_omega_form (Real.cos (θ / 2)) (Real.sin (θ / 2)) φ
  rw [hΩ, W4b_HooftMonopole_conjT]
  have h1 : Complex.exp (Complex.I * φ) * Complex.exp (-(Complex.I * φ)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hCS : ((Real.cos (θ / 2) : ℝ) : ℂ) ^ 2 + ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq (θ / 2)
    exact_mod_cast this
  exact W4b_HooftMonopole_unit_aux _ _ _ _ _ h1 hCS Complex.I_mul_I

theorem W4b_HooftMonopole_omega_adjoint_action (θ φ : ℝ) :
    omegaMatrix θ φ * pauli 2 * (omegaMatrix θ φ).conjTranspose =
      ((Real.sin θ * Real.sin φ : ℝ) : ℂ) • pauli 0
        + ((Real.sin θ * Real.cos φ : ℝ) : ℂ) • pauli 1
        + ((Real.cos θ : ℝ) : ℂ) • pauli 2 := by
  have hΩ : omegaMatrix θ φ =
      !![((Real.cos (θ / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * φ),
          ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I;
        ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I,
          ((Real.cos (θ / 2) : ℝ) : ℂ) * Complex.exp (-(Complex.I * φ))] :=
    W4b_HooftMonopole_omega_form (Real.cos (θ / 2)) (Real.sin (θ / 2)) φ
  have hp2 : pauli 2 = !![1, 0; 0, -1] := rfl
  rw [W4b_HooftMonopole_rhs_form, hΩ, W4b_HooftMonopole_conjT, hp2]
  have h1 : Complex.exp (Complex.I * φ) * Complex.exp (-(Complex.I * φ)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hE : Complex.exp (Complex.I * φ) =
      ((Real.cos φ : ℝ) : ℂ) + Complex.I * ((Real.sin φ : ℝ) : ℂ) := by
    rw [mul_comm Complex.I (φ : ℂ), Complex.exp_mul_I]; push_cast; ring
  have hE' : Complex.exp (-(Complex.I * φ)) =
      ((Real.cos φ : ℝ) : ℂ) - Complex.I * ((Real.sin φ : ℝ) : ℂ) := by
    rw [show -(Complex.I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul (θ / 2)
    have h2 := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    linarith
  have hA : ((Real.sin θ * Real.sin φ : ℝ) : ℂ) =
      2 * ((Real.sin (θ / 2) : ℝ) : ℂ) * ((Real.cos (θ / 2) : ℝ) : ℂ) * ((Real.sin φ : ℝ) : ℂ) := by
    rw [hs]; push_cast; ring
  have hB : ((Real.sin θ * Real.cos φ : ℝ) : ℂ) =
      2 * ((Real.sin (θ / 2) : ℝ) : ℂ) * ((Real.cos (θ / 2) : ℝ) : ℂ) * ((Real.cos φ : ℝ) : ℂ) := by
    rw [hs]; push_cast; ring
  have hD : ((Real.cos θ : ℝ) : ℂ) =
      ((Real.cos (θ / 2) : ℝ) : ℂ) ^ 2 - ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 := by
    rw [hc]; push_cast; ring
  rw [hA, hB, hD]
  have key := W4b_HooftMonopole_adj_aux ((Real.cos (θ / 2) : ℝ) : ℂ) ((Real.sin (θ / 2) : ℝ) : ℂ)
    (Complex.exp (Complex.I * φ)) (Complex.exp (-(Complex.I * φ))) Complex.I
    ((Real.cos φ : ℝ) : ℂ) ((Real.sin φ : ℝ) : ℂ) h1 Complex.I_mul_I hE hE'
  refine key.trans ?_
  refine W4b_HooftMonopole_fin2_eq ?_ ?_ ?_ ?_ <;> ring
