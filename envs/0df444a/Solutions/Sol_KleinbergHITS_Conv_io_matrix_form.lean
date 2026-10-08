-- Prove2me | solution 1 for KleinbergHITS.Conv.io_matrix_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T21:10:25.141592+00:00
-- url     : https://prove2.me/submissions/c501bb94-02e9-4a27-b413-8992929a8c83

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

open Matrix
open KleinbergHITS.Conv

theorem solution {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] :
    (∀ y : Fin n → ℝ, opI E y = (adjMatrix E)ᵀ *ᵥ y) ∧
      (∀ x : Fin n → ℝ, opO E x = adjMatrix E *ᵥ x) := by
  constructor
  · intro y
    ext p
    -- opI = filtered sum of y; Aᵀ mulVec y expands to ∑ j, y j * A j p
    change (∑ q ∈ Finset.univ.filter (fun q => E q p), y q) =
      ((adjMatrix E)ᵀ *ᵥ y) p
    simp only [mulVec, transpose_apply, adjMatrix, Finset.sum_filter, mul_ite, mul_one, mul_zero]
    -- both sides: ∑ q, if E q p then y q else 0  (up to mul_comm on the RHS)
    refine Finset.sum_congr rfl ?_
    intro q _
    by_cases h : E q p <;> simp [h, mul_comm]
  · intro x
    ext p
    change (∑ q ∈ Finset.univ.filter (fun q => E p q), x q) =
      (adjMatrix E *ᵥ x) p
    simp only [mulVec, adjMatrix, Finset.sum_filter, mul_ite, mul_one, mul_zero]
    refine Finset.sum_congr rfl ?_
    intro q _
    by_cases h : E p q <;> simp [h, mul_comm]
