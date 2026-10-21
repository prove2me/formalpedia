-- Prove2me | solution 2 for LittleCharity.MMS.efx_half_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:38:50.501273+00:00
-- url     : https://prove2.me/submissions/5d8b54ab-0615-4355-8925-3a4421464129

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

set_option autoImplicit false
open LittleCharity.MMS

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hEFX : IsEFX v X) (i j : Fin n)
    (hj : 2 ≤ (X j).card) :
    (1 - 1 / ((X j).card : ℝ)) * v i (X j) ≤ v i (X i) ∧
      (1 / 2 : ℝ) * v i (X j) ≤ v i (X i) := by
  classical
  have hc : (2 : ℝ) ≤ ((X j).card : ℝ) := by exact_mod_cast hj
  have hcpos : (0 : ℝ) < ((X j).card : ℝ) := by linarith
  have hV : 0 ≤ v i (X j) := hadd.2 i _
  -- for every g ∈ X j : v i (X j) - v i {g} ≤ v i (X i)
  have hg : ∀ g ∈ X j, v i (X j) - v i {g} ≤ v i (X i) := by
    intro g hg
    have h1 := hEFX i j g hg
    have h2 : v i ((X j).erase g) = v i (X j) - v i {g} := by
      rw [hadd.1 i ((X j).erase g), hadd.1 i (X j), Finset.sum_erase_eq_sub hg]
    linarith
  have hsum : ((X j).card : ℝ) * v i (X j) - v i (X j) ≤ ((X j).card : ℝ) * v i (X i) := by
    have h3 : ∑ g ∈ X j, (v i (X j) - v i {g}) ≤ ∑ _g ∈ X j, v i (X i) :=
      Finset.sum_le_sum hg
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      ← hadd.1 i (X j)] at h3
    exact h3
  have h1 : (1 - 1 / ((X j).card : ℝ)) * v i (X j) ≤ v i (X i) := by
    have : (1 - 1 / ((X j).card : ℝ)) * v i (X j)
        = (((X j).card : ℝ) * v i (X j) - v i (X j)) / ((X j).card : ℝ) := by
      field_simp
    rw [this, div_le_iff₀ hcpos]
    linarith
  refine ⟨h1, ?_⟩
  have h4 : (1 / 2 : ℝ) ≤ 1 - 1 / ((X j).card : ℝ) := by
    have : 1 / ((X j).card : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hc
    linarith
  calc (1 / 2 : ℝ) * v i (X j) ≤ (1 - 1 / ((X j).card : ℝ)) * v i (X j) :=
        mul_le_mul_of_nonneg_right h4 hV
    _ ≤ v i (X i) := h1
