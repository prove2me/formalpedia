-- Prove2me | solution 1 for Matrix.exists_specialLinearGroup_mul_upperTriangular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/da7cda20-ff9e-51e9-ae7e-b3d7a27dd590

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_specialLinearGroup_mul_upperTriangular

p2m_open "Matrix P2MW.S_Matrix_exists_specialLinearGroup_mul_upperTriangular.Matrix"

namespace Matrix
p2m_export "Matrix" "SpecialLinearGroup.coe_mul ext row SpecialLinearGroup det_fin_two SpecialLinearGroup.coe_one det_fin_two_of det_mul det of mul_apply"
p2m_open "Matrix"

theorem S06W2.exists_specialLinearGroup_mul_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    ∃ (B : SpecialLinearGroup (Fin 2) ℤ) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < |d| ∧ a * d = M.det ∧
      M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by

  set x := M 0 0 with hx
  set y := M 1 0 with hy
  have hxy : ¬ (x = 0 ∧ y = 0) := by
    rintro ⟨h0, h1⟩
    apply hM
    rw [det_fin_two, ← hx, ← hy, h0, h1, zero_mul, mul_zero, sub_zero]
  set g : ℤ := (Int.gcd x y : ℤ) with hg
  have hg0 : 0 < g := by
    rw [hg, Int.natCast_pos, Int.gcd_pos_iff]
    tauto
  obtain ⟨x', hx'⟩ : (g : ℤ) ∣ x := Int.gcd_dvd_left x y
  obtain ⟨y', hy'⟩ : (g : ℤ) ∣ y := Int.gcd_dvd_right x y

  set u := Int.gcdA x y
  set v := Int.gcdB x y
  have hbez : x * u + y * v = g := (Int.gcd_eq_gcd_ab x y).symm
  have hbez' : x' * u + y' * v = 1 := by
    rw [hx', hy'] at hbez
    have h0 : g * (x' * u + y' * v - 1) = 0 := by linear_combination hbez
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hg0.ne'
    · linear_combination h

  let B₀ : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![u, v; -y', x'], by rw [det_fin_two_of]; linear_combination hbez'⟩
  set b' := u * M 0 1 + v * M 1 1 with hb'
  set d := -y' * M 0 1 + x' * M 1 1 with hd
  have hkey : (B₀ : Matrix (Fin 2) (Fin 2) ℤ) * M = !![g, b'; 0, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B₀, Matrix.mul_apply, Fin.sum_univ_two, ← hx, ← hy, hx', hy', hb', hd] <;> ring_nf
    · linear_combination (g : ℤ) * hbez'

  have hdet : g * d = M.det := by
    have := congrArg Matrix.det hkey
    rw [det_mul, B₀.prop, one_mul, det_fin_two_of, mul_zero, sub_zero] at this
    exact this.symm
  have hd0 : d ≠ 0 := by intro h0; exact hM (by rw [← hdet, h0, mul_zero])

  set q := b' / d
  set r := b' % d
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hd0
  have hrd : r < |d| := Int.emod_lt_abs _ hd0
  have hbqr : b' = r + d * q := by
    have := Int.mul_ediv_add_emod b' d
    linear_combination -this
  let T : SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, q; 0, 1], by rw [det_fin_two_of]; ring⟩
  have hT : (T : Matrix (Fin 2) (Fin 2) ℤ) * !![g, r; 0, d] = !![g, b'; 0, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two, hbqr]
    ring
  refine ⟨B₀⁻¹ * T, g, r, d, hg0, hr0, hrd, hdet, ?_⟩
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hT, ← hkey, ← Matrix.mul_assoc,
    ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, Matrix.one_mul]

end Matrix

theorem solution (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < |d| ∧ a * d = M.det ∧ M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] :=
  Matrix.S06W2.exists_specialLinearGroup_mul_upperTriangular M hM

end S_Matrix_exists_specialLinearGroup_mul_upperTriangular
end P2MW
export P2MW.S_Matrix_exists_specialLinearGroup_mul_upperTriangular (solution)
