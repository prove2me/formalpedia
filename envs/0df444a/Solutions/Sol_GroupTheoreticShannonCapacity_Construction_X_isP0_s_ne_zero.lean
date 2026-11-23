-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.X_isP0_s_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:52:34.045586+00:00
-- url     : https://prove2.me/submissions/cf0ad4a5-1f91-48c7-8e51-fe600a8100ef

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_alpha_in_range
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_factorization
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_diagonal_left
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_diagonal_right
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_smul_pos
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__isP0_c8d2d6fe8993


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) (hs : s ≠ 0) :
    P0Matrix.IsP0Matrix n ((matrixX n k b r s).map (↑· : ℚ → ℝ)) := by
  -- Use the factorization X = scalar · D · M_α · D⁻¹
  -- Step 1: Get α ∈ [0,1]
  have hα := alpha_in_range n k b r s hn hk hb hrb
  have hα_ge : (0 : ℝ) ≤ (r : ℝ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n) := by
    have h := hα.1; exact_mod_cast h
  have hα_le : (r : ℝ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n) ≤ 1 := by
    have h := hα.2; exact_mod_cast h
  -- Step 2: M_α is P₀ (from MAlpha.Mα_isP0)
  have hMα : P0Matrix.IsP0Matrix n (MAlpha.Mα n
      ((r : ℝ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n))) :=
    MAlpha.Mα_isP0 n _ hα_ge hα_le
  -- Step 3: Conjugation by positive diagonal preserves P₀
  have ha_pos : (0 : ℝ) < (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) := by
    simp only [a]; positivity
  have hs_pos : (0 : ℝ) < (s : ℝ) := by positivity
  have hdiag_pos :
      ∀ i : Fin n, 0 < ((s : ℝ) / (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)) ^ (i.val : ℕ) := by
    intro i; exact pow_pos (div_pos hs_pos ha_pos) _
  have hconj : P0Matrix.IsP0Matrix n
      (diagPow n ((s : ℝ)/(a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))) *
       MAlpha.Mα n ((r : ℝ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n)) *
       diagPow n ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)/(s : ℝ))) := by
    -- Use P0Matrix.isP0_diagonal_left and isP0_diagonal_right
    -- First show D_{s/a} * M_α is P₀, then (D_{s/a} * M_α) * D_{a/s} is P₀
    have hd1_nonneg :
        ∀ i : Fin n, 0 ≤ ((s : ℝ) / (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)) ^ (i.val : ℕ) := by
      intro i; exact le_of_lt (pow_pos (div_pos hs_pos ha_pos) _)
    have hd2_nonneg :
        ∀ i : Fin n, 0 ≤ ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) / (s : ℝ)) ^ (i.val : ℕ) := by
      intro i; exact le_of_lt (pow_pos (div_pos ha_pos hs_pos) _)
    have hleft : P0Matrix.IsP0Matrix n
        (diagPow n ((s : ℝ)/(a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))) *
         MAlpha.Mα n ((r : ℝ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n))) := by
      unfold diagPow
      exact P0Matrix.isP0_diagonal_left n _ hMα _ hd1_nonneg
    unfold diagPow at hleft ⊢
    exact P0Matrix.isP0_diagonal_right n _ hleft _ hd2_nonneg
  -- Step 4: Scalar multiplication by positive scalar preserves P₀
  have hscalar_pos : (0 : ℝ) < (k : ℝ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)^(n-1) / (s : ℝ) := by
    apply div_pos
    · apply mul_pos
      · positivity
      · exact pow_pos ha_pos _
    · exact hs_pos
  -- Step 5: Apply factorization and conclude
  have hfact := X_factorization n k b r s hn hk hb hs
  simp only at hfact
  rw [hfact]
  exact GroupTheoreticShannonCapacity.P0Matrix.isP0_smul_pos n _ hconj _ hscalar_pos
end GroupTheoreticShannonCapacity.Construction
