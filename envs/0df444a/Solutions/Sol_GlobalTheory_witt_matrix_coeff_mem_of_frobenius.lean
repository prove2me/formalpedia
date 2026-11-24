-- Prove2me | solution 1 for GlobalTheory.witt_matrix_coeff_mem_of_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:38.93178+00:00
-- url     : https://prove2.me/submissions/ddbbfce8-1ce6-4e3d-b4c9-1a400fa063d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
import Theorems.Thm_GlobalTheory_WittIntegrality_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open WittIntegrality
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [CharP C p] [PerfectRing C p] (A : ValuationSubring C) {n : Type} [Fintype n] (Z : Matrix n n (WittVector p C)) (Y : Matrix n n (WittVector p A)), (Z.map WittVector.frobenius = Y.map (WittVector.map A.subtype) * Z ∨ Z.map WittVector.frobenius = Z * Y.map (WittVector.map A.subtype)) → ∀ i j m, (Z i j).coeff m ∈ A := by
  intro p _ C _ _ _ A n _ Z Y h i j m
  rcases h with h | h
  · refine key A (Y.map (WittVector.map A.subtype)) (fun i j => ⟨Y i j, rfl⟩) m Z 0
      (fun _ _ => Subring.zero_mem _) ?_ i j
    intro i j
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [this, Matrix.zero_apply, add_zero]
  · refine key A (Y.map (WittVector.map A.subtype)).transpose (fun i j => ⟨Y j i, rfl⟩) m
      Z.transpose 0 (fun _ _ => Subring.zero_mem _) ?_ j i
    intro i j
    have := congrFun (congrFun h j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [Matrix.transpose_apply, this, Matrix.zero_apply, add_zero]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
end GlobalTheory
