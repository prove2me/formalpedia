-- Prove2me | solution 1 for GroverWiki.groverMatrix_success_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T23:04:14.012105+00:00
-- url     : https://prove2.me/submissions/d4e41a50-c4d5-4c99-9f59-62a3589d9c59

import Mathlib
import Definitions.Def_GroverWiki_Defs
import Theorems.Thm_GroverWiki_groverMatrix_success_amplitude_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open GroverWiki

theorem solution {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    ‖![(1 : ℂ), 1 / (Real.sqrt N : ℂ)] ⬝ᵥ ((!![1, 2 / (Real.sqrt N : ℂ); -2 / (Real.sqrt N : ℂ), 1 - 4 / (N : ℂ)] ^ r) *ᵥ ![0, 1])‖ ^ 2 =
      Real.sin ((2 * r + 1) * Real.arcsin (1 / Real.sqrt N)) ^ 2 := by
  classical
  let t : ℝ := Real.arcsin (1 / Real.sqrt (N : ℝ))
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
    !![1, 2 / (Real.sqrt N : ℂ); -2 / (Real.sqrt N : ℂ), 1 - 4 / (N : ℂ)]
  let q : Fin 2 → ℂ := ![(1 : ℂ), 1 / (Real.sqrt N : ℂ)]
  let e : Fin 2 → ℂ := ![0, 1]
  have hNpos : 0 < N := by omega
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  have hNreal1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 / Real.sqrt (N : ℝ) ≤ 1 := by
    apply (div_le_one hroot).2
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N), hNreal1]
  have hxpos : 0 < 1 / Real.sqrt (N : ℝ) := one_div_pos.2 hroot
  have hxneg : -(1 : ℝ) ≤ 1 / Real.sqrt (N : ℝ) := by linarith
  have hsin : Real.sin t = 1 / Real.sqrt (N : ℝ) := by
    dsimp [t]
    exact Real.sin_arcsin hxneg hx1
  by_cases hN1 : N = 1
  · subst N
    exact GroverWiki.groverMatrix_success_amplitude_one r
  · have hN2 : 2 ≤ N := by omega
    have hroot_gt : 1 < Real.sqrt (N : ℝ) := by
      have hsqr := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)
      have hNreal2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      nlinarith
    have hxlt : 1 / Real.sqrt (N : ℝ) < 1 := (div_lt_one hroot).2 hroot_gt
    have hcos : 0 < Real.cos t := by
      rw [show t = Real.arcsin (1 / Real.sqrt (N : ℝ)) by rfl, Real.cos_arcsin]
      apply Real.sqrt_pos.2
      nlinarith [sq_nonneg (1 / Real.sqrt (N : ℝ)), hxpos, hxlt]
    have hsinC : (Real.sin t : ℂ) = 1 / (Real.sqrt N : ℂ) := by
      rw [hsin, Complex.ofReal_div, Complex.ofReal_one]
    have hsquareR : Real.sin t ^ 2 = 1 / (N : ℝ) := by
      rw [hsin]
      have hsqrt : (Real.sqrt (N : ℝ)) ^ 2 = N :=
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)
      field_simp [ne_of_gt hroot]
      nlinarith [hsqrt]
    have hsquare : (Real.sin t : ℂ) ^ 2 = 1 / (N : ℂ) := by
      simpa [Complex.ofReal_pow, Complex.ofReal_div] using congrArg Complex.ofReal hsquareR
    have hcoef : (2 : ℂ) / (Real.sqrt N : ℂ) = 2 * (Real.sin t : ℂ) := by rw [hsinC]; ring
    have hcoefNeg : (-2 : ℂ) / (Real.sqrt N : ℂ) = -2 * (Real.sin t : ℂ) := by rw [hsinC]; ring
    have hdiag : (1 : ℂ) - 4 / (N : ℂ) = 1 - 4 * (Real.sin t : ℂ) ^ 2 := by rw [div_eq_mul_one_div, ← hsquare]
    have hM (v : Fin 2 → ℂ) : M *ᵥ v = ![v 0 + 2 * (Real.sin t : ℂ) * v 1, -2 * (Real.sin t : ℂ) * v 0 + (1 - 4 * (Real.sin t : ℂ) ^ 2) * v 1] := by
      ext i
      fin_cases i
      · simp only [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one, Matrix.of_apply]
        rw [hcoef, one_mul]
      · simp only [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero', Fin.mk_zero, Fin.mk_one]
        change (-2 / (Real.sqrt N : ℂ)) * v 0 + (1 - 4 / (N : ℂ)) * v 1 = -2 * (Real.sin t : ℂ) * v 0 + (1 - 4 * (Real.sin t : ℂ) ^ 2) * v 1
        rw [hcoefNeg, hdiag]
    let c : ℝ := Real.cos t
    have hc : c ≠ 0 := ne_of_gt hcos
    have hstep0 (k : ℕ) :
        Real.sin (2 * (k : ℝ) * t + 2 * t) / c =
          Real.sin (2 * (k : ℝ) * t) / c + 2 * Real.sin t * (Real.cos (2 * (k : ℝ) * t + t) / c) := by
      dsimp [c]
      rw [Real.sin_add, Real.sin_two_mul, Real.cos_add, Real.cos_two_mul]
      field_simp [hc]
      linear_combination (2 * Real.sin (2 * (k : ℝ) * t)) * (Real.sin_sq_add_cos_sq t)
    have hstep1gen (x : ℝ) :
        -2 * Real.sin t * (Real.sin (x - t) / c) +
            (1 - 4 * Real.sin t ^ 2) * (Real.cos x / c) =
          Real.cos (x + 2 * t) / c := by
      rw [Real.cos_add, Real.sin_sub, Real.cos_two_mul, Real.sin_two_mul]
      field_simp [hc]
      linear_combination (-2 * Real.cos x) * (Real.sin_sq_add_cos_sq t)
    have hstep1 (k : ℕ) :
        -2 * Real.sin t * (Real.sin (2 * (k : ℝ) * t) / c) +
            (1 - 4 * Real.sin t ^ 2) * (Real.cos (2 * (k : ℝ) * t + t) / c) =
          Real.cos (2 * (k : ℝ) * t + t + 2 * t) / c := by
      have g := hstep1gen (2 * (k : ℝ) * t + t)
      have e : ((2 * (k : ℝ) * t + t) - t) = (2 * (k : ℝ) * t) := by ring
      rw [e] at g
      exact g
    have hvec (k : ℕ) : M ^ k *ᵥ e = ![((Real.sin (2 * (k : ℝ) * t) / c : ℝ) : ℂ), ((Real.cos ((2 * (k : ℝ) + 1) * t) / c : ℝ) : ℂ)] := by
      induction k with
      | zero =>
        ext i
        fin_cases i <;> simp [e, c, Real.sin_zero, Real.cos_zero, hc]
      | succ k ih =>
        have hk : M ^ (k + 1) *ᵥ e = M *ᵥ (M ^ k *ᵥ e) := by
          calc
            M ^ (k + 1) *ᵥ e = (M * M ^ k) *ᵥ e := by rw [pow_succ']
            _ = M *ᵥ (M ^ k *ᵥ e) := by rw [Matrix.mulVec_mulVec]
        rw [hk, ih, hM]
        have b1 : 2 * (((k + 1 : ℕ)) : ℝ) * t = 2 * (k : ℝ) * t + 2 * t := by
          push_cast
          ring
        have b2 : (2 * (k : ℝ) + 1) * t = 2 * (k : ℝ) * t + t := by ring
        have b3 : (2 * (((k + 1 : ℕ)) : ℝ) + 1) * t = (2 * (k : ℝ) * t + t) + 2 * t := by
          push_cast
          ring
        have h0 := hstep0 k
        rw [← b1, ← b2] at h0
        have h1 := hstep1 k
        rw [← b3, ← b2] at h1
        congr 1
        · simpa [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
            Complex.ofReal_ofNat, Complex.ofReal_natCast, Complex.ofReal_neg, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one] using (congrArg Complex.ofReal h0).symm
        · congr 1
          · simpa [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub,
              Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_natCast, Complex.ofReal_neg, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one] using congrArg Complex.ofReal h1
    have hreal (u : ℝ) : Real.sin u / c + Real.sin t * (Real.cos (u + t) / c) = Real.sin (u + t) := by
      dsimp [c]
      field_simp [hc]
      rw [Real.sin_add, Real.cos_add]
      linear_combination -(Real.sin u) * (Real.sin_sq_add_cos_sq t)
    have hamp : q ⬝ᵥ (M ^ r *ᵥ e) = (Real.sin ((2 * (r : ℝ) + 1) * t) : ℂ) := by
      rw [hvec]
      simp only [q, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_one, one_mul]
      rw [← hsinC]
      change ((Real.sin (2 * (r : ℝ) * t) / c : ℝ) : ℂ) + (Real.sin t : ℂ) * ((Real.cos ((2 * (r : ℝ) + 1) * t) / c : ℝ) : ℂ) = (Real.sin ((2 * (r : ℝ) + 1) * t) : ℂ)
      rw [show (2 * (r : ℝ) + 1) * t = 2 * (r : ℝ) * t + t by ring]
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div] using
        congrArg Complex.ofReal (hreal (2 * (r : ℝ) * t))
    have hang : (2 * (r : ℝ) + 1) * t = ((2 * r + 1 : ℕ) : ℝ) * Real.arcsin (1 / Real.sqrt (N : ℝ)) := by
      dsimp [t]
      push_cast
      ring
    rw [hamp, hang]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
