-- Prove2me | solution 1 for ModernConvex.Relaxations.quadform_eq_schurFormRat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:17:50.539247+00:00
-- url     : https://prove2.me/submissions/d6118831-37c8-46b0-b42f-096e9edaff5f

import Mathlib
import Definitions.Def_ModernConvex_SchurFormRat

/-!
# The Schur form over `ℚ`

The PSD oracle must run over the rationals: its output is a rational certificate, its case splits
must be decidable, and the machine that executes it is a rational-arithmetic machine. This file
gives the rational version of the Schur form at a pivot and the completing-the-square identity.

Everything here is pure field algebra — no order, no analysis — so the statements and proofs are
the ones of the real case verbatim.
-/

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **Completing the square, over `ℚ`.** -/
theorem quadform_eq_schurFormRat_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} (hM : M.IsHermitian)
    (i : Fin n) (ha : M i i ≠ 0) (v : Fin n → ℚ) :
    v ⬝ᵥ (M *ᵥ v)
      = M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2
        + schurFormRat M i v := by
  have hsymm : ∀ j : Fin n, M j i = M i j := by
    intro j
    simpa using (hM.apply j i).symm
  have hL : v ⬝ᵥ (M *ᵥ v) = ∑ p, ∑ q, v p * (M p q * v q) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  rw [hL, schurFormRat]
  have houter : ∑ p, ∑ q, v p * (M p q * v q)
      = (∑ q, v i * (M i q * v q))
        + ∑ p ∈ Finset.univ.erase i, ∑ q, v p * (M p q * v q) := by
    rw [← Finset.add_sum_erase Finset.univ (fun p => ∑ q, v p * (M p q * v q))
      (Finset.mem_univ i)]
  have hinner_i : ∑ q, v i * (M i q * v q)
      = v i * (M i i * v i) + ∑ q ∈ Finset.univ.erase i, v i * (M i q * v q) := by
    rw [← Finset.add_sum_erase Finset.univ (fun q => v i * (M i q * v q))
      (Finset.mem_univ i)]
  have hinner_rest : ∀ p : Fin n, ∑ q, v p * (M p q * v q)
      = v p * (M p i * v i) + ∑ q ∈ Finset.univ.erase i, v p * (M p q * v q) := by
    intro p
    rw [← Finset.add_sum_erase Finset.univ (fun q => v p * (M p q * v q))
      (Finset.mem_univ i)]
  rw [houter, hinner_i]
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ.erase i) => hinner_rest p)]
  rw [Finset.sum_add_distrib]
  have hA : ∑ q ∈ Finset.univ.erase i, v i * (M i q * v q)
      = v i * ∑ j ∈ Finset.univ.erase i, M i j * v j := by
    rw [Finset.mul_sum]
  have hB : ∑ p ∈ Finset.univ.erase i, v p * (M p i * v i)
      = v i * ∑ j ∈ Finset.univ.erase i, M i j * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hsymm p]
    ring
  have hR : M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2
      + ((∑ p ∈ Finset.univ.erase i, ∑ q ∈ Finset.univ.erase i, v p * (M p q * v q))
          - (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j) ^ 2)
      = M i i * v i ^ 2 + 2 * v i * (∑ j ∈ Finset.univ.erase i, M i j * v j)
        + ∑ p ∈ Finset.univ.erase i, ∑ q ∈ Finset.univ.erase i, v p * (M p q * v q) := by
    field_simp
    ring
  rw [hA, hB, hR]
  ring

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} (hM : M.IsHermitian)
    (i : Fin n) (ha : M i i ≠ 0) (v : Fin n → ℚ) :
    v ⬝ᵥ (M *ᵥ v)
      = M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2
        + schurFormRat M i v :=
  ModernConvex.Relaxations.quadform_eq_schurFormRat_proof hM i ha v
