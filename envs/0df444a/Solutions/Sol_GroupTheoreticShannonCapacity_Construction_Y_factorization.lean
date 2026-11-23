-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.Y_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:45:28.72588+00:00
-- url     : https://prove2.me/submissions/482666e7-85dd-4910-b78f-5e95d54505ef

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
section
namespace GroupTheoreticShannonCapacity.Construction
open Matrix
private lemma Y_factorization_upper_eq (n : ℕ) (k b r : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (i j : Fin n) (hij : (i : ℕ) < (j : ℕ)) :
    -(k : ℝ) * (b : ℝ) ^ (n - 1) * ((b : ℝ)⁻¹) ^ (i : ℕ) *
      ((r : ℝ) / ((k : ℝ) * (b : ℝ) ^ n)) * (b : ℝ) ^ (j : ℕ) =
    -(r : ℝ) * (b : ℝ) ^ ((j : ℕ) - (i : ℕ) - 1) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hk_ne : (k : ℝ) ≠ 0 := by positivity
  have hbn_ne : (b : ℝ) ^ n ≠ 0 := pow_ne_zero n hb_ne
  have hj_lt_n : (j : ℕ) < n := j.isLt
  rw [inv_pow]
  have hexp : (n - 1 : ℕ) + (j : ℕ) = (i : ℕ) + n + ((j : ℕ) - (i : ℕ) - 1) := by omega
  have key : (b : ℝ) ^ (n - 1) * (b : ℝ) ^ (j : ℕ) =
      (b : ℝ) ^ (i : ℕ) * (b : ℝ) ^ n * (b : ℝ) ^ ((j : ℕ) - (i : ℕ) - 1) := by
    rw [← pow_add, ← pow_add, ← pow_add, hexp]
  field_simp
  -- Goal: -(b^(n-1) * r * b^j) = -(b^i * r * b^n * b^(j-i-1))
  calc -((b : ℝ) ^ (n - 1) * (r : ℝ) * (b : ℝ) ^ (j : ℕ))
      = -((r : ℝ) * ((b : ℝ) ^ (n - 1) * (b : ℝ) ^ (j : ℕ))) := by ring
    _ = -((r : ℝ) * ((b : ℝ) ^ (i : ℕ) * (b : ℝ) ^ n *
        (b : ℝ) ^ ((j : ℕ) - (i : ℕ) - 1))) := by rw [key]
    _ = -((b : ℝ) ^ (i : ℕ) * (r : ℝ) * (b : ℝ) ^ n *
        (b : ℝ) ^ ((j : ℕ) - (i : ℕ) - 1)) := by ring
private lemma Y_factorization_lower_eq (n : ℕ) (k b _r : ℕ) (hn : 1 ≤ n) (_hk : 1 ≤ k) (hb : 1 ≤ b)
    (i j : Fin n) (hij : (i : ℕ) > (j : ℕ)) :
    -(k : ℝ) * (b : ℝ) ^ (n - 1) * ((b : ℝ)⁻¹) ^ (i : ℕ) * (-1) * (b : ℝ) ^ (j : ℕ) =
    (k : ℝ) * (b : ℝ) ^ (n - ((i : ℕ) - (j : ℕ) + 1)) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hi_lt_n : (i : ℕ) < n := i.isLt
  rw [inv_pow]
  have hexp : (n - 1 : ℕ) + (j : ℕ) = (i : ℕ) + (n - ((i : ℕ) - (j : ℕ) + 1)) := by omega
  have key : (b : ℝ) ^ (n - 1) * (b : ℝ) ^ (j : ℕ) =
      (b : ℝ) ^ (i : ℕ) * (b : ℝ) ^ (n - ((i : ℕ) - (j : ℕ) + 1)) := by
    rw [← pow_add, ← pow_add, hexp]
  field_simp
  rw [key]
section Tests
example : a 2 1 2 1 0 = 5 := by decide
example : p 2 1 2 1 0 = 5 := by
  simp only [p, a]
  norm_num
example : q 2 1 2 1 0 = 2 := by
  simp only [q, a]
  norm_num
example : p 2 1 2 1 0 = q 2 1 2 1 0 * 0 + 1 * (a 2 1 2 1 0)^(2-1) := by
  simp only [p, q, a]
  norm_num
example : p 2 1 2 1 0 * 2 = q 2 1 2 1 0 * (a 2 1 2 1 0) - 1 * 0^(2-1) := by
  simp only [p, q, a]
  norm_num
end Tests
end GroupTheoreticShannonCapacity.Construction
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    let α : ℝ := (r : ℝ) / ((k : ℝ) * (b : ℝ)^n)
    let scalar : ℝ := -(k : ℝ) * (b : ℝ)^(n-1)
    (matrixY n k b r s).map (↑· : ℚ → ℝ) =
      scalar • (diagPow n (b : ℝ)⁻¹ * MAlpha.Mα n α * diagPow n (b : ℝ)) := by
  intro α scalar
  ext i j
  simp only [Matrix.map_apply, matrixY, Matrix.of_apply]
  simp only [diagPow]
  simp_rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [MAlpha.Mα, Matrix.of_apply]
  rcases Nat.lt_trichotomy (i : ℕ) (j : ℕ) with hij_lt | hij_eq | hij_gt
  · -- Case i < j: upper triangular
    simp only [Y_entry, hij_lt, ↓reduceIte]
    have h := Y_factorization_upper_eq n k b r hn hk hb i j hij_lt
    push_cast
    simp only [smul_eq_mul]
    rw [← h]
    ring
  · -- Case i = j: diagonal (both sides are 0)
    have hi_eq_j : i = j := Fin.ext (by omega)
    subst hi_eq_j
    simp only [Y_entry, lt_self_iff_false, ↓reduceIte]
    simp only [Rat.cast_zero, inv_pow, mul_zero, zero_mul, smul_eq_mul]
  · -- Case i > j: lower triangular
    have hij_not_lt : ¬((i : ℕ) < (j : ℕ)) := by omega
    simp only [Y_entry, hij_not_lt, hij_gt, ↓reduceIte]
    have h := Y_factorization_lower_eq n k b r hn hk hb i j hij_gt
    push_cast
    simp only [smul_eq_mul]
    rw [← h]
    ring
end GroupTheoreticShannonCapacity.Construction
