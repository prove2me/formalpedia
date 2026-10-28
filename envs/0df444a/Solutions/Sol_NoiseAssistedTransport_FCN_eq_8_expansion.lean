-- Prove2me | solution 1 for NoiseAssistedTransport.FCN.eq_8_expansion
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:11:29.745195+00:00
-- url     : https://prove2.me/submissions/408c6b59-1c46-4487-9fec-b0e975bd90ab

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

open NoiseAssistedTransport.FCN in
theorem solution (N : ℕ) (hN : 2 ≤ N) :
    ket N 1 = ((1 / ((N : ℝ) - 1) : ℝ) : ℂ) •
      ((∑ j ∈ Finset.Icc 2 (N - 1), psiState N j) + ((Real.sqrt N : ℝ) : ℂ) • phiState N
        - ket N N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hM1 : M + 2 - 1 = M + 1 := by omega
  rw [hM1]
  unfold psiState phiState
  have hs : (((Real.sqrt ((M + 2 : ℕ) : ℝ)) : ℝ) : ℂ) * (((Real.sqrt ((M + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀]
    · simp
    · apply Real.sqrt_ne_zero'.mpr
      positivity
  rw [smul_smul, hs, one_smul]
  have hsplit : ∑ j ∈ Finset.Icc 1 (M + 2), ket (M + 2) j =
      ket (M + 2) 1 + ∑ j ∈ Finset.Icc 2 (M + 1), ket (M + 2) j + ket (M + 2) (M + 2) := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1 + 1)]
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ M + 1)]
    rw [Finset.sum_insert (by simp)]
    rfl
  rw [hsplit, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  have hc : (M + 1 + 1 - 2 : ℕ) = M := by omega
  rw [hc]
  have e : (M • ket (M + 2) 1 - ∑ j ∈ Finset.Icc 2 (M + 1), ket (M + 2) j) +
      (ket (M + 2) 1 + ∑ j ∈ Finset.Icc 2 (M + 1), ket (M + 2) j + ket (M + 2) (M + 2)) -
      ket (M + 2) (M + 2) = ((M : ℂ) + 1) • ket (M + 2) 1 := by
    rw [add_smul, one_smul, ← Nat.cast_smul_eq_nsmul ℂ]
    abel
  rw [e, smul_smul]
  have hr : (((1 / (((M + 2 : ℕ) : ℝ) - 1)) : ℝ) : ℂ) * ((M : ℂ) + 1) = 1 := by
    push_cast
    have : ((M : ℂ) + 2 - 1) = (M : ℂ) + 1 := by ring
    rw [this]
    field_simp
  rw [hr, one_smul]
