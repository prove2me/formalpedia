-- Prove2me | solution 1 for GroverWiki.groverMatrix_jordan_form
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:29:54.663845+00:00
-- url     : https://prove2.me/submissions/530a02fa-cc5e-42ec-8a92-2fb6b43130a4

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Positivity
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (hN : 2 ≤ N) :
    let t : ℝ := Real.arcsin (1 / Real.sqrt N)
    let A : Matrix (Fin 2) (Fin 2) ℂ :=
      !![1, 2 / (Real.sqrt N : ℂ); -2 / (Real.sqrt N : ℂ), 1 - 4 / (N : ℂ)]
    let M : Matrix (Fin 2) (Fin 2) ℂ :=
      !![-Complex.I, Complex.I; Complex.exp (t * Complex.I), Complex.exp (-(t * Complex.I))]
    A = M * !![Complex.exp (2 * t * Complex.I), 0; 0, Complex.exp (-(2 * t * Complex.I))] * M⁻¹ ∧
      ∀ r : ℕ, A ^ r =
        M * !![Complex.exp (2 * r * t * Complex.I), 0;
              0, Complex.exp (-(2 * r * t * Complex.I))] * M⁻¹ := by
  classical
  dsimp only
  let t : ℝ := Real.arcsin (1 / Real.sqrt N)
  let q : ℝ := Real.sqrt N
  let c : ℝ := Real.cos t
  let s : ℝ := 1 / q
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    !![1, 2 / (q : ℂ); -2 / (q : ℂ), 1 - 4 / (N : ℂ)]
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
    !![-Complex.I, Complex.I; Complex.exp (t * Complex.I), Complex.exp (-(t * Complex.I))]
  let D (r : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
    !![Complex.exp (2 * r * t * Complex.I), 0;
       0, Complex.exp (-(2 * r * t * Complex.I))]
  suffices hmain : A = M * D 1 * M⁻¹ ∧ ∀ r : ℕ, A ^ r = M * D r * M⁻¹ by
    simpa only [A, M, D, Nat.cast_one, mul_one, t, q] using hmain
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hq1 : 1 < q := by nlinarith
  have hq : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq1)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s < 1 := by dsimp [s]; exact (div_lt_one (by positivity)).2 hq1
  have hsin : Real.sin t = s := by
    have hx0 : (-1 : ℝ) ≤ 1 / Real.sqrt N := by
      have hxnonneg : 0 ≤ 1 / Real.sqrt N := by positivity
      linarith
    have hx1 : 1 / Real.sqrt N ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact le_of_lt hq1
    simpa [t, s, q] using Real.sin_arcsin hx0 hx1
  have htrig : c ^ 2 + s ^ 2 = 1 := by
    simpa [c, hsin, add_comm] using Real.sin_sq_add_cos_sq t
  have hc0 : 0 ≤ c := Real.cos_arcsin_nonneg _
  have hc : c ≠ 0 := by intro hz; rw [hz] at htrig; nlinarith
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hq2c : (q : ℂ) ^ 2 = N := by exact_mod_cast hq2
  have htrigc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast htrig
  have hsC : (s : ℂ) = 1 / (q : ℂ) := by simp [s]
  have hsinC : Complex.sin (t : ℂ) = (s : ℂ) := by
    apply Complex.ext
    · simpa [Complex.sin_ofReal_re] using hsin
    · simp [Complex.sin_ofReal_im]
  have he : Complex.exp (t * Complex.I) = (c : ℂ) + (s : ℂ) * Complex.I := by
    simp [Complex.exp_mul_I, c, hsinC]
  have hen : Complex.exp (-(t * Complex.I)) = (c : ℂ) - (s : ℂ) * Complex.I := by
    rw [show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp [c, hsinC, sub_eq_add_neg]
  have he2 : Complex.exp (2 * t * Complex.I) = ((c : ℂ) + (s : ℂ) * Complex.I) ^ 2 := by
    rw [show (2 : ℂ) * t * Complex.I = (t * Complex.I) + (t * Complex.I) by ring,
      Complex.exp_add, he, pow_two]
  have hen2 : Complex.exp (-(2 * t * Complex.I)) = ((c : ℂ) - (s : ℂ) * Complex.I) ^ 2 := by
    rw [show -((2 : ℂ) * t * Complex.I) = -(t * Complex.I) + -(t * Complex.I) by ring,
      Complex.exp_add, hen, pow_two]
  have hdet : M.det ≠ 0 := by
    have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hd : M.det = (-2 * Complex.I) * (c : ℂ) := by
      simp [M, Matrix.det_fin_two, he, hen]
      ring
    rw [hd]
    exact mul_ne_zero (by simp) hcc
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have htwo : (2 : ℂ) / q = 2 * (s : ℂ) := by rw [hsC]; ring
  have hfour : (4 : ℂ) / N = 4 * (s : ℂ)^2 := by
    rw [hsC, ← hq2c]
    field_simp
  have hAM : A * M = M * D 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, M, D, Matrix.mul_apply, Fin.sum_univ_two, he, hen, he2, hen2,
        htwo, hfour, show (-2 : ℂ) / q = -(2 / q) by ring]
    all_goals apply Complex.ext
    all_goals simp [Complex.mul_re, Complex.mul_im, pow_two, pow_succ]
    all_goals nlinarith [congrArg Complex.re htrigc,
      congrArg (fun x : ℝ => c * x) htrig,
      congrArg (fun x : ℝ => s * x) htrig]
  have hA : A = M * D 1 * M⁻¹ := by
    calc
      A = A * (M * M⁻¹) := by rw [hMi, mul_one]
      _ = (A * M) * M⁻¹ := by rw [mul_assoc]
      _ = M * D 1 * M⁻¹ := by rw [hAM]
  have hD0 : D 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [D]
  have hDsucc (r : ℕ) : D (r + 1) = D r * D 1 := by
    have hp : (2 : ℂ) * (r + 1 : ℕ) * t * Complex.I =
        2 * r * t * Complex.I + 2 * t * Complex.I := by push_cast; ring
    have hm : -((2 : ℂ) * (r + 1 : ℕ) * t * Complex.I) =
        -(2 * r * t * Complex.I) + -(2 * t * Complex.I) := by push_cast; ring
    have hpos : Complex.exp ((2 : ℂ) * (r + 1 : ℕ) * t * Complex.I) =
        Complex.exp ((2 : ℂ) * r * t * Complex.I) * Complex.exp (2 * t * Complex.I) := by
      rw [hp, Complex.exp_add]
    have hneg : Complex.exp (-((2 : ℂ) * (r + 1 : ℕ) * t * Complex.I)) =
        Complex.exp (-(2 * r * t * Complex.I)) * Complex.exp (-(2 * t * Complex.I)) := by
      rw [hm, Complex.exp_add]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [D, Matrix.mul_apply, Fin.sum_univ_two] using hpos
    · simp [D, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [D, Matrix.mul_apply, Fin.sum_univ_two]
    · simpa [D, Matrix.mul_apply, Fin.sum_univ_two] using hneg
  refine ⟨hA, ?_⟩
  intro r
  induction r with
  | zero => simp [hD0, hMi]
  | succ r ih =>
      calc
        A ^ (r + 1) = A ^ r * A := by rw [pow_succ]
        _ = (M * D r * M⁻¹) * (M * D 1 * M⁻¹) := by rw [ih, hA]
        _ = (M * D r) * (D 1 * M⁻¹) := by
          rw [mul_assoc]
          have hcancel : M⁻¹ * (M * D 1 * M⁻¹) = D 1 * M⁻¹ := by
            calc
              M⁻¹ * (M * D 1 * M⁻¹) = (M⁻¹ * M) * D 1 * M⁻¹ := by
                simp only [mul_assoc]
              _ = D 1 * M⁻¹ := by rw [hiM, one_mul]
          simpa only [hcancel] using rfl
        _ = M * (D r * D 1) * M⁻¹ := by simp only [mul_assoc]
        _ = M * D (r + 1) * M⁻¹ := by rw [← hDsucc]
