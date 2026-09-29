-- Prove2me | solution 1 for GiuntiStudenikin2015.msw_diagonalization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T09:50:58.078182+00:00
-- url     : https://prove2.me/submissions/ee8163b5-6cbd-499c-8432-a2e7cb8add0f

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem gs15_rot_diag (k A B R c s C2 S2 : ℝ) (hc2 : c ^ 2 - s ^ 2 = C2) (hs2 : 2 * s * c = S2)
    (hA : R * C2 = A) (hB : R * S2 = B) (hp : C2 ^ 2 + S2 ^ 2 = 1) :
    Matrix.transpose !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)] *
        ((k : ℂ) • !![((-A : ℝ) : ℂ), (B : ℂ); (B : ℂ), (A : ℂ)]) *
        !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)] =
      (k : ℂ) • Matrix.diagonal ![((-R : ℝ) : ℂ), (R : ℂ)] := by
  have hc2' : (c : ℂ) ^ 2 - (s : ℂ) ^ 2 = (C2 : ℂ) := by exact_mod_cast hc2
  have hs2' : 2 * (s : ℂ) * (c : ℂ) = (S2 : ℂ) := by exact_mod_cast hs2
  have hA' : (R : ℂ) * (C2 : ℂ) = (A : ℂ) := by exact_mod_cast hA
  have hB' : (R : ℂ) * (S2 : ℂ) = (B : ℂ) := by exact_mod_cast hB
  have hp' : (C2 : ℂ) ^ 2 + (S2 : ℂ) ^ 2 = 1 := by exact_mod_cast hp
  have d00 : Matrix.diagonal ![((-R : ℝ) : ℂ), (R : ℂ)] 0 0 = -(R : ℂ) := by simp
  have d01 : Matrix.diagonal ![((-R : ℝ) : ℂ), (R : ℂ)] 0 1 = 0 := by simp
  have d10 : Matrix.diagonal ![((-R : ℝ) : ℂ), (R : ℂ)] 1 0 = 0 := by simp
  have d11 : Matrix.diagonal ![((-R : ℝ) : ℂ), (R : ℂ)] 1 1 = (R : ℂ) := by simp
  have u00 : !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)] 0 0 = (c : ℂ) := rfl
  have u01 : !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)] 0 1 = (s : ℂ) := rfl
  have u10 : !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)] 1 0 = -(s : ℂ) := rfl
  have u11 : !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)] 1 1 = (c : ℂ) := rfl
  have h00 : !![((-A : ℝ) : ℂ), (B : ℂ); (B : ℂ), (A : ℂ)] 0 0 = -(A : ℂ) := by
    show ((-A : ℝ) : ℂ) = -(A : ℂ); push_cast; ring
  have h01 : !![((-A : ℝ) : ℂ), (B : ℂ); (B : ℂ), (A : ℂ)] 0 1 = (B : ℂ) := rfl
  have h10 : !![((-A : ℝ) : ℂ), (B : ℂ); (B : ℂ), (A : ℂ)] 1 0 = (B : ℂ) := rfl
  have h11 : !![((-A : ℝ) : ℂ), (B : ℂ); (B : ℂ), (A : ℂ)] 1 1 = (A : ℂ) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, u00, u01, u10, u11, h00, h01, h10,
      h11, d00, d01, d10, d11]
  · linear_combination (k : ℂ) * (-(A : ℂ) * hc2' - (B : ℂ) * hs2' + (C2 : ℂ) * hA' +
      (S2 : ℂ) * hB' - (R : ℂ) * hp')
  · linear_combination (k : ℂ) * ((B : ℂ) * hc2' - (A : ℂ) * hs2' + (S2 : ℂ) * hA' -
      (C2 : ℂ) * hB')
  · linear_combination (k : ℂ) * ((B : ℂ) * hc2' - (A : ℂ) * hs2' + (S2 : ℂ) * hA' -
      (C2 : ℂ) * hB')
  · linear_combination (k : ℂ) * ((A : ℂ) * hc2' + (B : ℂ) * hs2' - (C2 : ℂ) * hA' -
      (S2 : ℂ) * hB' + (R : ℂ) * hp')

open GiuntiStudenikin2015 in
theorem solution (dm2 θ E Vcc : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2) (hE : 0 < E) :
    Matrix.transpose (twoFlavorMixing (mswMixingAngle dm2 θ E Vcc)) * mswHamiltonian dm2 θ E Vcc *
        twoFlavorMixing (mswMixingAngle dm2 θ E Vcc) =
      ((1 / (4 * E) : ℝ) : ℂ) •
        Matrix.diagonal ![((-mswDeltaM2 dm2 θ E Vcc : ℝ) : ℂ), ((mswDeltaM2 dm2 θ E Vcc : ℝ) : ℂ)] := by
  have hR : mswDeltaM2 dm2 θ E Vcc =
      ‖(⟨dm2 * Real.cos (2 * θ) - 2 * E * Vcc, dm2 * Real.sin (2 * θ)⟩ : ℂ)‖ := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    rfl
  have h2φ : Complex.arg (⟨dm2 * Real.cos (2 * θ) - 2 * E * Vcc, dm2 * Real.sin (2 * θ)⟩ : ℂ) =
      2 * mswMixingAngle dm2 θ E Vcc := by
    unfold mswMixingAngle
    ring
  have hmix : twoFlavorMixing (mswMixingAngle dm2 θ E Vcc) =
      !![(Real.cos (mswMixingAngle dm2 θ E Vcc) : ℂ), (Real.sin (mswMixingAngle dm2 θ E Vcc) : ℂ);
        -(Real.sin (mswMixingAngle dm2 θ E Vcc) : ℂ), (Real.cos (mswMixingAngle dm2 θ E Vcc) : ℂ)] :=
    rfl
  have hH : mswHamiltonian dm2 θ E Vcc = ((1 / (4 * E) : ℝ) : ℂ) •
      !![((-(dm2 * Real.cos (2 * θ) - 2 * E * Vcc) : ℝ) : ℂ), ((dm2 * Real.sin (2 * θ) : ℝ) : ℂ);
        ((dm2 * Real.sin (2 * θ) : ℝ) : ℂ), ((dm2 * Real.cos (2 * θ) - 2 * E * Vcc : ℝ) : ℂ)] := by
    unfold mswHamiltonian
    rw [show -dm2 * Real.cos (2 * θ) + 2 * E * Vcc = -(dm2 * Real.cos (2 * θ) - 2 * E * Vcc) by ring]
  rw [hmix, hH]
  refine gs15_rot_diag _ _ _ _ _ _
    (Real.cos (Complex.arg (⟨dm2 * Real.cos (2 * θ) - 2 * E * Vcc, dm2 * Real.sin (2 * θ)⟩ : ℂ)))
    (Real.sin (Complex.arg (⟨dm2 * Real.cos (2 * θ) - 2 * E * Vcc, dm2 * Real.sin (2 * θ)⟩ : ℂ)))
    ?_ ?_ ?_ ?_ ?_
  · rw [h2φ, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (mswMixingAngle dm2 θ E Vcc)
    linarith
  · rw [h2φ, Real.sin_two_mul]
  · rw [hR]
    exact Complex.norm_mul_cos_arg _
  · rw [hR]
    exact Complex.norm_mul_sin_arg _
  · exact Real.cos_sq_add_sin_sq _
