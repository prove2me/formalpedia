-- Prove2me | solution 1 for ModernConvex.Relaxations.schurForm_extendAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:33:13.873204+00:00
-- url     : https://prove2.me/submissions/f54602d4-5c67-4b86-9351-33882b9c8c3f

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurForm
import Definitions.Def_ModernConvex_SchurStep
import Theorems.Thm_ModernConvex_Relaxations_sum_erase_eq_sum_subtype

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The Schur form of the extended vector is the quadratic form of the Schur step.** -/
theorem schurForm_extendAt_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (w : {j : Fin n // j ≠ i} → ℝ) :
    schurForm M i (extendAt i w) = w ⬝ᵥ (schurStep M i *ᵥ w) := by
  have hsymm : ∀ j : Fin n, M j i = M i j := by
    intro j
    simpa using (hM.apply j i).symm
  -- the Schur form, reindexed
  have key : schurForm M i (extendAt i w)
      = (∑ j : {j : Fin n // j ≠ i}, ∑ k : {k : Fin n // k ≠ i},
            w j * (M j.1 k.1 * w k))
        - (M i i)⁻¹ * (∑ j : {j : Fin n // j ≠ i}, M i j.1 * w j) ^ 2 := by
    unfold schurForm
    rw [sum_erase_eq_sum_subtype i
      (fun j => ∑ k ∈ Finset.univ.erase i, extendAt i w j * (M j k * extendAt i w k))]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_erase_eq_sum_subtype i
        (fun k => extendAt i w j.1 * (M j.1 k * extendAt i w k))]
      exact Finset.sum_congr rfl fun k _ => by
        rw [extendAt_of_ne i w j.2, extendAt_of_ne i w k.2]
    · congr 1
      congr 1
      rw [sum_erase_eq_sum_subtype i (fun j => M i j * extendAt i w j)]
      exact Finset.sum_congr rfl fun j _ => by rw [extendAt_of_ne i w j.2]
  -- the quadratic form of the Schur step, expanded
  have key2 : w ⬝ᵥ (schurStep M i *ᵥ w)
      = (∑ j : {j : Fin n // j ≠ i}, ∑ k : {k : Fin n // k ≠ i},
            w j * (M j.1 k.1 * w k))
        - (M i i)⁻¹ * (∑ j : {j : Fin n // j ≠ i}, M i j.1 * w j) ^ 2 := by
    -- expand the left side into a double sum of differences
    have hexp : w ⬝ᵥ (schurStep M i *ᵥ w)
        = ∑ x : {x : Fin n // x ≠ i}, ∑ y : {y : Fin n // y ≠ i},
            (w x * (M x.1 y.1 * w y)
              - (M i i)⁻¹ * ((w x * M x.1 i) * (M i y.1 * w y))) := by
      simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum, schurStep]
      exact Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun y _ => by ring
    -- split the double sum
    have hsplit : (∑ x : {x : Fin n // x ≠ i}, ∑ y : {y : Fin n // y ≠ i},
          (w x * (M x.1 y.1 * w y)
            - (M i i)⁻¹ * ((w x * M x.1 i) * (M i y.1 * w y))))
        = (∑ x : {x : Fin n // x ≠ i}, ∑ y : {y : Fin n // y ≠ i},
            w x * (M x.1 y.1 * w y))
          - ∑ x : {x : Fin n // x ≠ i}, ∑ y : {y : Fin n // y ≠ i},
              (M i i)⁻¹ * ((w x * M x.1 i) * (M i y.1 * w y)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_sub_distrib]
    -- factor the second piece as a square
    have hsq : (∑ x : {x : Fin n // x ≠ i}, ∑ y : {y : Fin n // y ≠ i},
          (M i i)⁻¹ * ((w x * M x.1 i) * (M i y.1 * w y)))
        = (M i i)⁻¹ * (∑ j : {j : Fin n // j ≠ i}, M i j.1 * w j) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hsymm x.1]
      ring
    rw [hexp, hsplit, hsq]

  rw [key, key2]

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (w : {j : Fin n // j ≠ i} → ℝ) :
    schurForm M i (extendAt i w) = w ⬝ᵥ (schurStep M i *ᵥ w) :=
  ModernConvex.Relaxations.schurForm_extendAt_proof hM i w
