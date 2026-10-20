-- Prove2me | solution 1 for Hintz2026.Cmat_10_eq
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:00:08.481573+00:00
-- url     : https://prove2.me/submissions/bfc5cbc2-5e4f-437c-86ef-884354d102d2

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_Cmat_eq_adj_form

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

noncomputable section

namespace Hintz2026
-- inlined helpers (local source: Atlas/Perturbations/Hintz2026/*.lean at 8d059e0)
variable (p : SubextremalKN)

theorem X00e (x : Fin 2 → ℝ) : X p x 0 0 = ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) / rhoBar p x := by simp [X]

theorem X01e (x : Fin 2 → ℝ) : X p x 0 1 = -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x) := by simp [X]

theorem X10e (x : Fin 2 → ℝ) : X p x 1 0 = I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p x) := by simp [X]

theorem X11e (x : Fin 2 → ℝ) : X p x 1 1 = ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) / rhoBarStar p x := by simp [X]

theorem star_X11 (x : Fin 2 → ℝ) : star (X p x 1 1) = ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) / rhoBar p x := by
  rw [X11e, star_def, map_div₀, map_mul, map_sub, map_mul, conj_ofReal, conj_ofReal, conj_ofReal, conj_ofReal, conj_rhoBarStar_eq]

theorem star_X01 (x : Fin 2 → ℝ) : star (X p x 0 1) = I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p x) := by
  rw [X01e]; simp [conj_ofReal, conj_rhoBar_eq, map_sub, map_div₀]

theorem adjX_00 (x : Fin 2 → ℝ) : adjugate (X p x) 0 0 = X p x 1 1 := by rw [adjugate_fin_two]; rfl

theorem adjX_01 (x : Fin 2 → ℝ) : adjugate (X p x) 0 1 = -(X p x 0 1) := by rw [adjugate_fin_two]; rfl

theorem adjX_10 (x : Fin 2 → ℝ) : adjugate (X p x) 1 0 = -(X p x 1 0) := by rw [adjugate_fin_two]; rfl

theorem adjX_11 (x : Fin 2 → ℝ) : adjugate (X p x) 1 1 = X p x 0 0 := by rw [adjugate_fin_two]; rfl

theorem adjXH_ij (x : Fin 2 → ℝ) (i j : Fin 2) : (adjugate (X p x))ᴴ i j = star (adjugate (X p x) j i) := conjTranspose_apply _ _ _

theorem triple_10 (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℝ) :
    (adjugate (X p x) * M * (adjugate (X p x))ᴴ) 1 0 =
      (-(X p x 1 0) * M 0 0 + X p x 0 0 * M 1 0) * star (X p x 1 1)
      + (-(X p x 1 0) * M 0 1 + X p x 0 0 * M 1 1) * (-star (X p x 0 1)) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, adjXH_ij, adjX_00, adjX_01, adjX_10, adjX_11, star_neg] <;> ring

theorem M00 (sg om mm : ℝ) (x : Fin 2 → ℝ) : (cscalar p sg om mm x • (1:Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 0 0 = cscalar p sg om mm x - I * bcoeff p sg om mm x := by simp [Bmat, Matrix.smul_apply]

theorem M01 (sg om mm : ℝ) (x : Fin 2 → ℝ) : (cscalar p sg om mm x • (1:Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 0 1 = -(I * (3 * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (↑p.Q * rhoBar p x))) := by simp [Bmat, Matrix.smul_apply]

theorem M10 (sg om mm : ℝ) (x : Fin 2 → ℝ) : (cscalar p sg om mm x • (1:Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 1 0 = -(I * (3 * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2)) := by simp [Bmat, Matrix.smul_apply]

theorem M11 (sg om mm : ℝ) (x : Fin 2 → ℝ) : (cscalar p sg om mm x • (1:Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 1 1 = cscalar p sg om mm x + I * bcoeff p sg om mm x := by simp [Bmat, Matrix.smul_apply]

theorem C10_times_k (sg om mm : ℝ) {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * Cmat p sg om mm x 1 0 =
      (adjugate (X p x) * (cscalar p sg om mm x • 1 - Bmat p sg om mm x) * (adjugate (X p x))ᴴ) 1 0 := by
  rw [Cmat_eq_adj_form p sg om mm hx, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast Q_sq_sub_M_sq_ne_zero p), one_mul]

theorem sep_10 (sg om mm : ℝ) {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * Cmat p sg om mm x 1 0 =
    ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (-R1coeff p sg om (x 0) + I * ↑(Th1coeff p sg om (x 1))) := by
  rw [C10_times_k p sg om mm hx, triple_10, M00, M01, M10, M11, star_X11, star_X01, X10e, X00e]
  unfold cscalar bcoeff R1coeff Th1coeff Kfreq Del'
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hk : (↑(p.M ^ 2 - p.Q ^ 2) : ℂ) ≠ 0 := by
    have := Q_sq_sub_M_sq_ne_zero p; intro h; apply this; have := Complex.ofReal_eq_zero.mp h; linarith
  have hk' : (↑p.M : ℂ) ^ 2 - (↑p.Q : ℂ) ^ 2 ≠ 0 := by push_cast at hk; exact hk
  have hrr : rhoBar p x = ↑(x 0) + ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBar_eq_ofReal]; push_cast; ring
  have hrrs : rhoBarStar p x = ↑(x 0) - ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBarStar_eq_ofReal]; push_cast; ring
  have hs3 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 3 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) := by rw [pow_succ, hsq, mul_comm]
  have hs4 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 4 = ↑(Del p (x 0)) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hsq]
  have hs5 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 5 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) ^ 2 := by rw [pow_succ, hs4, mul_comm]
  have hs6 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 6 = ↑(Del p (x 0)) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hsq]
  have htrig : (↑(Real.sin (x 1)) : ℂ) ^ 2 + (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.sin_sq_add_cos_sq]; rfl
  have hcos2 : (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 - (↑(Real.sin (x 1)) : ℂ) ^ 2 := by linear_combination htrig
  have hc3 : (↑(Real.cos (x 1)) : ℂ) ^ 3 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) := by rw [pow_succ, hcos2, mul_comm]
  have hc4 : (↑(Real.cos (x 1)) : ℂ) ^ 4 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hcos2]
  have hc5 : (↑(Real.cos (x 1)) : ℂ) ^ 5 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [pow_succ, hc4, mul_comm]
  have hc6 : (↑(Real.cos (x 1)) : ℂ) ^ 6 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hcos2]
  have hI5 : (I : ℂ) ^ 5 = I := by rw [pow_succ, I_pow_four, one_mul]
  have hI6 : (I : ℂ) ^ 6 = -1 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, I_sq]; norm_num
  have hI7 : (I : ℂ) ^ 7 = -I := by rw [pow_succ, hI6]; ring
  have hI8 : (I : ℂ) ^ 8 = 1 := by rw [show (8:ℕ) = 4*2 from rfl, pow_mul, I_pow_four, one_pow]
  push_cast at *
  field_simp [hr, hrs, hDne, hsD, hs, hQ, hk, hk']
  rw [hrr, hrrs]
  ring_nf
  simp only [hsq, hs3, hs4, hs5, hs6, hcos2, hc3, hc4, hc5, hc6]
  simp only [Del]
  push_cast
  ring_nf
  simp only [I_sq, I_pow_three, I_pow_four, hI5, hI6, hI7, hI8]
  ring_nf

theorem k_ne : ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Q_sq_sub_M_sq_ne_zero p

theorem Csep_10 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Csep p sg om mm x 1 0 = -R1coeff p sg om (x 0) + I * ↑(Th1coeff p sg om (x 1)) := by
  simp [Csep, Rmat, Thmat, Matrix.smul_apply]

end Hintz2026

open Hintz2026 in
theorem solution (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x 1 0 = Csep p sg om mm x 1 0 :=
  by
    rw [Csep_10]; exact mul_left_cancel₀ (k_ne p) (sep_10 p sg om mm hx)

end
