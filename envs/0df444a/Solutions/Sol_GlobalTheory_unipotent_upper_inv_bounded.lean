-- Prove2me | solution 1 for GlobalTheory.unipotent_upper_inv_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:39.205685+00:00
-- url     : https://prove2.me/submissions/955d17be-e08d-47db-9e5b-a7ec55155fb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  intro N C
  refine ⟨(Nat.factorial N : ℝ) * (max C 1) ^ N, ?_⟩
  intro n hd hl hb
  have htri : n.BlockTriangular id := fun i j h => hl i j h
  have hdet : n.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]; simp [hd]
  have hu : IsUnit n.det := by rw [hdet]; exact isUnit_one
  refine ⟨n⁻¹, Matrix.nonsing_inv_mul n hu, Matrix.mul_nonsing_inv n hu, ?_, ?_⟩
  · intro i j h
    letI := Matrix.invertibleOfIsUnitDet n hu
    exact Matrix.blockTriangular_inv_of_blockTriangular htri h
  · intro i j
    have hinv : n⁻¹ = n.adjugate := by rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have key := Matrix.det_le (abv := AbsoluteValue.abs) (x := max C 1)
      (A := n.updateRow j (Pi.single i 1)) ?_
    · simpa using key
    · intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self, Pi.single_apply]
        split_ifs <;> simp
      · rw [Matrix.updateRow_ne hk]
        exact le_trans (hb k l) (le_max_left _ _)
end GlobalTheory
