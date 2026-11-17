-- Prove2me | solution 1 for N25.matrix_det25_triangular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:27.481639+00:00
-- url     : https://prove2.me/submissions/334595f4-fafe-4fb7-8e12-7df7f9b77bcf

import Mathlib

set_option autoImplicit false

open Matrix

namespace N25

/-- Positive integral triangularization for the dilation at every cusp. -/
theorem _root_.solution (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 25) :
    ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : ℕ) (e v : ℤ),
      d = Int.gcd (M 0 0) (M 1 0) ∧ 0 < d ∧ 0 < e ∧ (d : ℤ) * e = 25 ∧
      M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![(d : ℤ), v; 0, e] := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 25 := by
    simpa only [Matrix.det_fin_two] using hM
  let d := Int.gcd (M 0 0) (M 1 0)
  have hd : 0 < d := by
    by_contra hn
    have hz : Int.gcd (M 0 0) (M 1 0) = 0 := by change d = 0; omega
    obtain ⟨ha, hc⟩ := Int.gcd_eq_zero_iff.mp hz
    simp [ha, hc] at hdet
  obtain ⟨x, y, hxy, hx, hy⟩ := Int.exists_gcd_one hd
  change M 0 0 = x * (d : ℤ) at hx
  change M 1 0 = y * (d : ℤ) at hy
  have hcop : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hxy
  obtain ⟨u, w, huw⟩ := hcop
  let B : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![x, -w; y, u], by rw [Matrix.det_fin_two_of]; linear_combination huw⟩
  let e : ℤ := -y * M 0 1 + x * M 1 1
  let v : ℤ := u * M 0 1 + w * M 1 1
  have hde : (d : ℤ) * e = 25 := by
    rw [hx, hy] at hdet
    dsimp [e]
    change x * (d : ℤ) * M 1 1 - M 0 1 * (y * (d : ℤ)) = 25 at hdet
    linear_combination hdet
  have he : 0 < e := by
    have hd' : (0 : ℤ) < d := by exact_mod_cast hd
    nlinarith
  refine ⟨B, d, e, v, rfl, hd, he, hde, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [B, Matrix.mul_apply, Fin.sum_univ_two]
  · change M 0 0 = x * (d : ℤ) + -w * 0
    simpa using hx
  · change M 0 1 = x * v + -w * e
    dsimp [v, e]
    linear_combination -(M 0 1) * huw
  · change M 1 0 = y * (d : ℤ) + u * 0
    simpa using hy
  · change M 1 1 = y * v + u * e
    dsimp [v, e]
    linear_combination -(M 1 1) * huw

end N25
