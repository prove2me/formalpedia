-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.matrixX_real_isP0_s_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:52:34.617015+00:00
-- url     : https://prove2.me/submissions/90aad302-15cf-4606-ad44-517baf73a75a

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_alpha_real_in_range
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_diagonal_left
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_diagonal_right
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_smul_pos
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__isP0_c8d2d6fe8993


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r : ℕ) (s : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) (hs : 0 < s) :
    P0Matrix.IsP0Matrix n (matrixX_real n k b r s) := by
  -- The proof: matrixX_real = scalar * D_{s/a} * M_α * D_{a/s}
  -- where α = r*s^n/(k*a^n) ∈ [0,1], so M_α is P₀
  -- Conjugation by positive diagonal and scaling by positive scalar preserves P₀
  -- Step 1: Get α ∈ [0,1]
  set a' := aReal n k b r s with ha'_def
  set α := (r : ℝ) * s^n / (k * a'^n) with hα_def
  have hα := alpha_real_in_range n k b r s hn hk hb hrb hs
  -- Step 2: M_α is P₀
  have hMα : P0Matrix.IsP0Matrix n (MAlpha.Mα n α) :=
    MAlpha.Mα_isP0 n α hα.1 hα.2
  -- Step 3: Conjugation by positive diagonal preserves P₀
  have ha_pos : 0 < a' := by unfold aReal at ha'_def; simp only [ha'_def]; positivity
  have hdiag_pos : ∀ i : Fin n, 0 < (s / a') ^ (i.val : ℕ) :=
    fun i => pow_pos (div_pos hs ha_pos) _
  have hd1_nonneg : ∀ i : Fin n, 0 ≤ (s / a') ^ (i.val : ℕ) :=
    fun i => le_of_lt (hdiag_pos i)
  have hd2_nonneg : ∀ i : Fin n, 0 ≤ (a' / s) ^ (i.val : ℕ) :=
    fun i => le_of_lt (pow_pos (div_pos ha_pos hs) _)
  have hconj : P0Matrix.IsP0Matrix n
      (diagPow n (s/a') * MAlpha.Mα n α * diagPow n (a'/s)) := by
    have hleft : P0Matrix.IsP0Matrix n (diagPow n (s/a') * MAlpha.Mα n α) := by
      unfold diagPow
      exact P0Matrix.isP0_diagonal_left n _ hMα _ hd1_nonneg
    unfold diagPow at hleft ⊢
    exact P0Matrix.isP0_diagonal_right n _ hleft _ hd2_nonneg
  -- Step 4: Scalar multiplication by positive scalar preserves P₀
  have hscalar_pos : 0 < (k : ℝ) * a'^(n-1) / s := by
    apply div_pos
    · apply mul_pos
      · positivity
      · exact pow_pos ha_pos _
    · exact hs
  -- Step 5: Show matrixX_real equals the factored form
  -- The factorization follows the same algebraic identities as X_factorization
  have hfact : matrixX_real n k b r s =
      ((k : ℝ) * a'^(n-1) / s) • (diagPow n (s/a') * MAlpha.Mα n α * diagPow n (a'/s)) := by
    ext i j
    simp only [matrixX_real, Matrix.of_apply, Matrix.smul_apply, diagPow]
    simp_rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [MAlpha.Mα, Matrix.of_apply, smul_eq_mul]
    have ha_ne : a' ≠ 0 := ne_of_gt ha_pos
    have hs_ne : s ≠ 0 := ne_of_gt hs
    have hk_ne : (k : ℝ) ≠ 0 := by positivity
    rcases Nat.lt_trichotomy (i : ℕ) (j : ℕ) with hij_lt | hij_eq | hij_gt
    · -- Upper triangular case: same algebraic identity as factorization_upper_eq
      simp only [X_entry_real, hij_lt, ↓reduceIte]
      rw [div_pow, div_pow]
      have hj_lt_n : (j : ℕ) < n := j.isLt
      have hji_ge_1 : 1 ≤ (j : ℕ) - (i : ℕ) := Nat.sub_pos_of_lt hij_lt
      have hjin_le : (j : ℕ) - (i : ℕ) + 1 ≤ n := by omega
      field_simp
      ring_nf
      simp only [ha'_def, hα_def]
      -- Exponent matching: collect powers of a and s
      -- LHS: r * a'^(j-i-1) * s * s^(n-1-(j-i)) * s^j * a'^i
      -- RHS: s^i * a'^j * a'^(n-1) * k * (r * s^n / (k * a'^n))
      -- After simplification, both equal r * a'^(j-1) * s^(n+i)
      have ha_pow_ne : a' ^ n ≠ 0 := pow_ne_zero n ha_ne
      -- Combine powers on LHS
      have ha_lhs : a' ^ ((j : ℕ) - (i : ℕ) - 1) * a' ^ (i : ℕ) = a' ^ ((j : ℕ) - 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hs_lhs : s * s ^ (n - (1 + ((j : ℕ) - (i : ℕ)))) * s ^ (j : ℕ) = s ^ (n + (i : ℕ)) := by
        conv_lhs => lhs; lhs; rw [← pow_one s]
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      -- Simplify RHS: k cancels with k in denominator
      have h_rhs : s ^ (i : ℕ) * a' ^ (j : ℕ) * a' ^ (n - 1) * (k : ℝ) *
          ((r : ℝ) * s ^ n / ((k : ℝ) * a' ^ n)) =
          (r : ℝ) * a' ^ ((j : ℕ) - 1) * s ^ (n + (i : ℕ)) := by
        field_simp
        -- Goal: s^i * a'^j * a'^(n-1) * r * s^n = r * a'^n * a'^(j-1) * s^(n+i)
        -- Both sides equal r * a'^(j+n-1) * s^(i+n)
        have hj_ge_1 : 1 ≤ (j : ℕ) := by omega
        have ha_lhs' : a' ^ (j : ℕ) * a' ^ (n - 1) = a' ^ ((j : ℕ) + (n - 1)) := by rw [pow_add]
        have ha_rhs' : a' ^ n * a' ^ ((j : ℕ) - 1) = a' ^ (n + ((j : ℕ) - 1)) := by rw [pow_add]
        have hs_lhs' : s ^ (i : ℕ) * s ^ n = s ^ ((i : ℕ) + n) := by rw [pow_add]
        have hexp_a : (j : ℕ) + (n - 1) = n + ((j : ℕ) - 1) := by omega
        have hexp_s : (i : ℕ) + n = n + (i : ℕ) := by omega
        calc s ^ (i : ℕ) * a' ^ (j : ℕ) * a' ^ (n - 1) * (r : ℝ) * s ^ n
            = (r : ℝ) * (a' ^ (j : ℕ) * a' ^ (n - 1)) * (s ^ (i : ℕ) * s ^ n) := by ring
          _ = (r : ℝ) * a' ^ ((j : ℕ) + (n - 1)) * s ^ ((i : ℕ) + n) := by rw [ha_lhs', hs_lhs']
          _ = (r : ℝ) * a' ^ (n + ((j : ℕ) - 1)) * s ^ (n + (i : ℕ)) := by rw [hexp_a, hexp_s]
          _ = (r : ℝ) * (a' ^ n * a' ^ ((j : ℕ) - 1)) * s ^ (n + (i : ℕ)) := by rw [← ha_rhs']
          _ = (r : ℝ) * a' ^ n * a' ^ ((j : ℕ) - 1) * s ^ (n + (i : ℕ)) := by ring
      -- Now prove the goal
      calc (r : ℝ) * a' ^ ((j : ℕ) - (i : ℕ) - 1) * s * s ^ (n - (1 + ((j : ℕ) - (i : ℕ)))) *
           s ^ (j : ℕ) * a' ^ (i : ℕ)
          = (r : ℝ) * (a' ^ ((j : ℕ) - (i : ℕ) - 1) * a' ^ (i : ℕ)) *
            (s * s ^ (n - (1 + ((j : ℕ) - (i : ℕ)))) * s ^ (j : ℕ)) := by ring
        _ = (r : ℝ) * a' ^ ((j : ℕ) - 1) * s ^ (n + (i : ℕ)) := by rw [ha_lhs, hs_lhs]
        _ = s ^ (i : ℕ) * a' ^ (j : ℕ) * a' ^ (n - 1) * (k : ℝ) *
            ((r : ℝ) * s ^ n / ((k : ℝ) * a' ^ n)) := by rw [← h_rhs]
    · -- Diagonal case
      have hi_eq_j : i = j := Fin.ext (by omega)
      subst hi_eq_j
      simp only [X_entry_real, lt_self_iff_false, ↓reduceIte]
      ring
    · -- Lower triangular case: same algebraic identity as factorization_lower_eq
      have hij_not_lt : ¬((i : ℕ) < (j : ℕ)) := by omega
      simp only [X_entry_real, hij_not_lt, hij_gt, ↓reduceIte]
      rw [div_pow, div_pow]
      field_simp
      ring_nf
      simp only [ha'_def]
      -- Goal: -(a'^(n-(1+(i-j))) * s * s^(i-j-1) * s^j * a'^i) = -(s^i * a'^j * a'^(n-1))
      -- Both sides are equal to -(a'^(n-1+j) * s^i)
      rw [neg_inj]
      have hi_lt_n : (i : ℕ) < n := i.isLt
      have hij_ge_1 : 1 ≤ (i : ℕ) - (j : ℕ) := Nat.sub_pos_of_lt hij_gt
      have hijn_le : (i : ℕ) - (j : ℕ) + 1 ≤ n := by omega
      -- Combine powers on LHS
      have ha_lhs :
          a' ^ (n - (1 + ((i : ℕ) - (j : ℕ)))) * a' ^ (i : ℕ) = a' ^ (n - 1 + (j : ℕ)) := by
        rw [← pow_add]
        congr 1
        omega
      have hs_lhs : s * s ^ ((i : ℕ) - (j : ℕ) - 1) * s ^ (j : ℕ) = s ^ (i : ℕ) := by
        conv_lhs => lhs; lhs; rw [← pow_one s]
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      -- Combine powers on RHS
      have ha_rhs : a' ^ (j : ℕ) * a' ^ (n - 1) = a' ^ ((j : ℕ) + (n - 1)) := by rw [pow_add]
      have hexp_a : (j : ℕ) + (n - 1) = n - 1 + (j : ℕ) := by omega
      calc a' ^ (n - (1 + ((i : ℕ) - (j : ℕ)))) * s * s ^ ((i : ℕ) - (j : ℕ) - 1) *
           s ^ (j : ℕ) * a' ^ (i : ℕ)
          = (a' ^ (n - (1 + ((i : ℕ) - (j : ℕ)))) * a' ^ (i : ℕ)) *
            (s * s ^ ((i : ℕ) - (j : ℕ) - 1) * s ^ (j : ℕ)) := by ring
        _ = a' ^ (n - 1 + (j : ℕ)) * s ^ (i : ℕ) := by rw [ha_lhs, hs_lhs]
        _ = s ^ (i : ℕ) * a' ^ ((j : ℕ) + (n - 1)) := by rw [hexp_a]; ring
        _ = s ^ (i : ℕ) * (a' ^ (j : ℕ) * a' ^ (n - 1)) := by rw [← ha_rhs]
        _ = s ^ (i : ℕ) * a' ^ (j : ℕ) * a' ^ (n - 1) := by ring
  rw [hfact]
  exact GroupTheoreticShannonCapacity.P0Matrix.isP0_smul_pos n _ hconj _ hscalar_pos
end GroupTheoreticShannonCapacity.Construction
