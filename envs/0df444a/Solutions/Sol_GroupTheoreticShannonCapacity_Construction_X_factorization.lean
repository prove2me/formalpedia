-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.X_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:31:48.484511+00:00
-- url     : https://prove2.me/submissions/4dcab785-4847-41f3-8b8b-3a6523b4bd05

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
section
namespace GroupTheoreticShannonCapacity.Construction
open Matrix
private lemma factorization_upper_eq (n : ℕ) (k b r s : ℕ) (_hn : 1 ≤ n) (_hk : 1 ≤ k) (_hb : 1 ≤ b)
    (_hs : s ≠ 0) (i j : Fin n) (_hij : (i : ℕ) < (j : ℕ)) :
    let a' : ℝ := a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    (k : ℝ) * a' ^ (n - 1) / (s : ℝ) * ((s : ℝ) / a') ^ (i : ℕ) *
    ((r : ℝ) * (s : ℝ) ^ n / ((k : ℝ) * a' ^ n)) * (a' / (s : ℝ)) ^ (j : ℕ) =
    (r : ℝ) * a' ^ ((j : ℕ) - (i : ℕ) - 1) * (s : ℝ) ^ (n - ((j : ℕ) - (i : ℕ) + 1)) := by
  -- Proof: cancel k, collect powers of a' and s, verify exponents match
  intro a'
  -- Establish positivity
  have hs_pos : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero _hs)
  have hk_pos : (0 : ℝ) < k := by positivity
  have ha_pos : (0 : ℝ) < a' := by
    change (0 : ℝ) < ↑(a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ))
    simp only [a]; push_cast; positivity
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have ha_ne : a' ≠ 0 := ne_of_gt ha_pos
  -- Establish bounds for natural subtraction
  have hij : (i : ℕ) < (j : ℕ) := _hij
  have hj_lt_n : (j : ℕ) < n := j.isLt
  have hji_ge_1 : 1 ≤ (j : ℕ) - (i : ℕ) := Nat.sub_pos_of_lt hij
  have hjin_le : (j : ℕ) - (i : ℕ) + 1 ≤ n := by omega
  -- Use power laws and simplify
  have ha_pow_n_ne : a' ^ n ≠ 0 := pow_ne_zero n ha_ne
  have ha_pow_i_ne : a' ^ (i : ℕ) ≠ 0 := pow_ne_zero (i : ℕ) ha_ne
  have hs_pow_j_ne : (s : ℝ) ^ (j : ℕ) ≠ 0 := pow_ne_zero (j : ℕ) hs_ne
  rw [div_pow, div_pow]
  field_simp
  -- Goal after field_simp:
  -- a' ^ (n - 1) * s ^ i * r * s ^ n * a' ^ j
  --   = s * a' ^ i * r * a' ^ n * s ^ j * a' ^ (j-i-1) * s ^ (n-(j-i+1))
  -- Collect powers using pow_add
  have ha_lhs : a' ^ (n - 1) * a' ^ (j : ℕ) = a' ^ (n - 1 + (j : ℕ)) := (pow_add a' _ _).symm
  have hs_lhs : (s : ℝ) ^ (i : ℕ) * (s : ℝ) ^ n = (s : ℝ) ^ ((i : ℕ) + n) := (pow_add _ _ _).symm
  have ha_rhs : a' ^ (i : ℕ) * a' ^ n * a' ^ ((j : ℕ) - (i : ℕ) - 1) =
      a' ^ ((i : ℕ) + n + ((j : ℕ) - (i : ℕ) - 1)) := by rw [← pow_add, ← pow_add]
  have hs_rhs : (s : ℝ) * (s : ℝ) ^ (j : ℕ) * (s : ℝ) ^ (n - ((j : ℕ) - (i : ℕ) + 1)) =
      (s : ℝ) ^ (1 + (j : ℕ) + (n - ((j : ℕ) - (i : ℕ) + 1))) := by
    conv_lhs => lhs; lhs; rw [← pow_one (s : ℝ)]
    rw [← pow_add, ← pow_add]
  -- Show exponents match using omega
  have hexp_a : n - 1 + (j : ℕ) = (i : ℕ) + n + ((j : ℕ) - (i : ℕ) - 1) := by omega
  have hexp_s : (i : ℕ) + n = 1 + (j : ℕ) + (n - ((j : ℕ) - (i : ℕ) + 1)) := by omega
  -- The goal after field_simp has the structure we need
  -- Use ring_nf to normalize, then rewrite with pow_add identities
  calc a' ^ (n - 1) * (s : ℝ) ^ (i : ℕ) * (r : ℝ) * (s : ℝ) ^ n * a' ^ (j : ℕ)
      = (r : ℝ) * (a' ^ (n - 1) * a' ^ (j : ℕ)) * ((s : ℝ) ^ (i : ℕ) * (s : ℝ) ^ n) := by ring
    _ = (r : ℝ) * a' ^ (n - 1 + (j : ℕ)) * (s : ℝ) ^ ((i : ℕ) + n) := by rw [ha_lhs, hs_lhs]
    _ = (r : ℝ) * a' ^ ((i : ℕ) + n + ((j : ℕ) - (i : ℕ) - 1)) *
        (s : ℝ) ^ (1 + (j : ℕ) + (n - ((j : ℕ) - (i : ℕ) + 1))) := by rw [hexp_a, hexp_s]
    _ = (r : ℝ) * (a' ^ (i : ℕ) * a' ^ n * a' ^ ((j : ℕ) - (i : ℕ) - 1)) *
        ((s : ℝ) * (s : ℝ) ^ (j : ℕ) * (s : ℝ) ^ (n - ((j : ℕ) - (i : ℕ) + 1))) := by
      rw [← ha_rhs, ← hs_rhs]
    _ = (s : ℝ) * a' ^ (i : ℕ) * (r : ℝ) * a' ^ n * (s : ℝ) ^ (j : ℕ) *
        a' ^ ((j : ℕ) - (i : ℕ) - 1) * (s : ℝ) ^ (n - ((j : ℕ) - (i : ℕ) + 1)) := by ring
private lemma factorization_lower_eq (n : ℕ) (k b r s : ℕ) (_hn : 1 ≤ n) (_hk : 1 ≤ k) (_hb : 1 ≤ b)
    (_hs : s ≠ 0) (i j : Fin n) (_hij : (i : ℕ) > (j : ℕ)) :
    let a' : ℝ := a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    (k : ℝ) * a' ^ (n - 1) / (s : ℝ) * ((s : ℝ) / a') ^ (i : ℕ) *
    (-1 : ℝ) * (a' / (s : ℝ)) ^ (j : ℕ) =
    -(k : ℝ) * a' ^ (n - ((i : ℕ) - (j : ℕ) + 1)) * (s : ℝ) ^ ((i : ℕ) - (j : ℕ) - 1) := by
  -- Proof: collect powers of a' and s, verify exponents match
  intro a'
  -- Establish positivity
  have hs_pos : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero _hs)
  have hk_pos : (0 : ℝ) < k := by positivity
  have ha_pos : (0 : ℝ) < a' := by
    change (0 : ℝ) < ↑(a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ))
    simp only [a]; push_cast; positivity
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have ha_ne : a' ≠ 0 := ne_of_gt ha_pos
  -- Establish bounds for natural subtraction
  have hij : (i : ℕ) > (j : ℕ) := _hij
  have hi_lt_n : (i : ℕ) < n := i.isLt
  have hij_ge_1 : 1 ≤ (i : ℕ) - (j : ℕ) := Nat.sub_pos_of_lt hij
  have hijn_le : (i : ℕ) - (j : ℕ) + 1 ≤ n := by omega
  -- Use power laws and simplify
  have ha_pow_n_ne : a' ^ n ≠ 0 := pow_ne_zero n ha_ne
  have ha_pow_j_ne : a' ^ (j : ℕ) ≠ 0 := pow_ne_zero (j : ℕ) ha_ne
  have hs_pow_i_ne : (s : ℝ) ^ (i : ℕ) ≠ 0 := pow_ne_zero (i : ℕ) hs_ne
  rw [div_pow, div_pow]
  field_simp
  -- Goal after field_simp:
  -- -(a'^(n-1) * s^i * a'^j) = -(s * a'^i * s^j * a'^(n-(i-j+1)) * s^(i-j-1))
  -- Both sides have negation, cancel it
  rw [neg_inj]
  -- Now prove: a'^(n-1) * s^i * a'^j = s * a'^i * s^j * a'^(n-(i-j+1)) * s^(i-j-1)
  -- Show exponents match using omega, then use congr_arg to lift to powers
  have hexp_a : n - 1 + (j : ℕ) = (i : ℕ) + (n - ((i : ℕ) - (j : ℕ) + 1)) := by omega
  have hexp_s : (i : ℕ) = 1 + (j : ℕ) + ((i : ℕ) - (j : ℕ) - 1) := by omega
  -- Combine powers on LHS: rearrange so a' powers are adjacent
  have lhs_eq : a' ^ (n - 1) * (s : ℝ) ^ (i : ℕ) * a' ^ (j : ℕ) =
      a' ^ (n - 1 + (j : ℕ)) * (s : ℝ) ^ (i : ℕ) := by
    calc a' ^ (n - 1) * (s : ℝ) ^ (i : ℕ) * a' ^ (j : ℕ)
        = a' ^ (n - 1) * a' ^ (j : ℕ) * (s : ℝ) ^ (i : ℕ) := by ring
      _ = a' ^ (n - 1 + (j : ℕ)) * (s : ℝ) ^ (i : ℕ) := by rw [pow_add]
  -- Combine powers on RHS: group a' and s powers separately
  have rhs_eq : (s : ℝ) * a' ^ (i : ℕ) * (s : ℝ) ^ (j : ℕ) *
      a' ^ (n - ((i : ℕ) - (j : ℕ) + 1)) * (s : ℝ) ^ ((i : ℕ) - (j : ℕ) - 1) =
      a' ^ ((i : ℕ) + (n - ((i : ℕ) - (j : ℕ) + 1))) *
      (s : ℝ) ^ (1 + (j : ℕ) + ((i : ℕ) - (j : ℕ) - 1)) := by
    calc (s : ℝ) * a' ^ (i : ℕ) * (s : ℝ) ^ (j : ℕ) *
         a' ^ (n - ((i : ℕ) - (j : ℕ) + 1)) * (s : ℝ) ^ ((i : ℕ) - (j : ℕ) - 1)
        = (a' ^ (i : ℕ) * a' ^ (n - ((i : ℕ) - (j : ℕ) + 1))) *
          ((s : ℝ) ^ 1 * (s : ℝ) ^ (j : ℕ) * (s : ℝ) ^ ((i : ℕ) - (j : ℕ) - 1)) := by
            rw [pow_one]; ring
      _ = a' ^ ((i : ℕ) + (n - ((i : ℕ) - (j : ℕ) + 1))) *
          ((s : ℝ) ^ (1 + (j : ℕ)) * (s : ℝ) ^ ((i : ℕ) - (j : ℕ) - 1)) := by
            rw [pow_add, pow_add]
      _ = a' ^ ((i : ℕ) + (n - ((i : ℕ) - (j : ℕ) + 1))) *
          (s : ℝ) ^ (1 + (j : ℕ) + ((i : ℕ) - (j : ℕ) - 1)) := by
            rw [← pow_add]
  rw [lhs_eq, rhs_eq, hexp_a, ← hexp_s]
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
theorem _root_.solution (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hs : s ≠ 0) :
    let α : ℝ := (r : ℝ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n)
    let a' : ℝ := a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    let scalar : ℝ := k * a'^(n-1) / s
    (matrixX n k b r s).map (↑· : ℚ → ℝ) =
      scalar • (diagPow n (s/a') * MAlpha.Mα n α * diagPow n (a'/s)) := by
  -- Proof by direct algebraic computation matching entries
  intro α a' scalar
  ext i j
  -- Simplify LHS: (matrixX n k b r s).map _ i j = X_entry n k b r s i j as ℝ
  simp only [Matrix.map_apply, matrixX, Matrix.of_apply]
  -- Simplify RHS using diagonal multiplication lemmas
  -- (D_1 * M * D_2)_{i,j} = D_1(i,i) * M(i,j) * D_2(j,j)
  simp only [diagPow]
  simp_rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [MAlpha.Mα, Matrix.of_apply]
  -- Now RHS is: scalar * (s/a')^i * (if i < j then α else if i > j then -1 else 0) * (a'/s)^j
  -- Split into three cases based on comparison of i and j
  rcases Nat.lt_trichotomy (i : ℕ) (j : ℕ) with hij_lt | hij_eq | hij_gt
  · -- Case i < j: upper triangular
    simp only [X_entry, hij_lt, ↓reduceIte]
    -- RHS: scalar • ((s/a')^i * α * (a'/s)^j)
    -- Now apply factorization_upper_eq
    have h := factorization_upper_eq n k b r s hn hk hb hs i j hij_lt
    push_cast
    simp only [smul_eq_mul]
    -- RHS is now: scalar * (s^i * s^(-1)^j * a'^j * a'^(-1)^i * α)
    -- LHS from h is: k * a'^(n-1) / s * (s/a')^i * α * (a'/s)^j = r * a'^(j-i-1) * s^(n-(j-i+1))
    -- We need to show that scalar * (s/a')^i * α * (a'/s)^j = r * a'^(j-i-1) * s^(n-(j-i+1))
    -- Since scalar = k * a'^(n-1) / s, this follows from h
    rw [← h]
    ring
  · -- Case i = j: diagonal (both sides are 0)
    have hi_eq_j : i = j := Fin.ext (by omega)
    subst hi_eq_j
    simp only [X_entry, lt_self_iff_false, ↓reduceIte]
    -- RHS: scalar • 0 = 0
    simp only [Rat.cast_zero, mul_zero, zero_mul, smul_eq_mul]
  · -- Case i > j: lower triangular
    have hij_not_lt : ¬((i : ℕ) < (j : ℕ)) := by omega
    simp only [X_entry, hij_not_lt, hij_gt, ↓reduceIte]
    -- RHS: scalar • ((s/a')^i * (-1) * (a'/s)^j)
    -- Now apply factorization_lower_eq
    have h := factorization_lower_eq n k b r s hn hk hb hs i j hij_gt
    push_cast
    simp only [smul_eq_mul]
    rw [← h]
    ring
end GroupTheoreticShannonCapacity.Construction
