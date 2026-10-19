-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.selectedMinor_row_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:45:59.653114+00:00
-- url     : https://prove2.me/submissions/17dd3cd6-3d3c-4be3-9c96-7b3d5503a126

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem solution
    {m K : ℕ} {v0 θ H : ℝ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ) (hH : 0 < H) :
    0 < (Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 θ
      (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) := by
  classical
  let w := OAI.PiExponent.MatrixArithmetic.logWeights q
  have hzero_mem :
      (0 : Fin (m + 1) → ℕ) ∈
        OAI.PiExponent.realWeightedSimplex
          (OAI.PiExponent.InterpolationMatrix.rowWeights v0 θ w) H := by
    simp [OAI.PiExponent.realWeightedSimplex]
    exact le_of_lt hH
  have hzero_strict :
      (0 : Fin (m + 1) → ℕ) ∈
        OAI.PiExponent.strictWeightedSimplex
          (OAI.PiExponent.InterpolationMatrix.rowWeights v0 θ w) H := by
    rw [OAI.PiExponent.strictWeightedSimplex, Finset.mem_filter]
    refine ⟨hzero_mem, ?_⟩
    simpa using hH
  have hrow : Nonempty (OAI.PiExponent.InterpolationMatrix.Row K v0 θ w H) := by
    exact ⟨⟨⟨0, by omega⟩, ⟨0, hzero_strict⟩⟩⟩
  have hcard :
      0 < Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 θ w H) :=
    Fintype.card_pos_iff.mpr hrow
  exact_mod_cast hcard