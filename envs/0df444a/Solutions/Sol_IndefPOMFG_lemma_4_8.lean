-- Prove2me | solution 1 for IndefPOMFG.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:45:59.582344+00:00
-- url     : https://prove2.me/submissions/b70aa136-984b-46ea-85c4-6aff20837a11

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_IndefPOMFG_Coeffs
import Definitions.Def_IndefPOMFG_Space
import Definitions.Def_IndefPOMFG_NPlayer
import Definitions.Def_IndefPOMFG_Limiting

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

theorem solution {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (S : Matrix (Fin n) (Fin m) ℝ) (hQ : Q.IsSymm) (hR : R.IsSymm) :
    (R.PosDef ∧ (Q - S * R⁻¹ * Sᵀ).PosSemidef) ↔
      (R.PosDef ∧ (Matrix.fromBlocks Q S Sᵀ R).PosSemidef) := by
  constructor
  · rintro ⟨hRp, h⟩
    letI := hRp.isUnit.invertible
    refine ⟨hRp, ?_⟩
    have key := Matrix.PosDef.fromBlocks₂₂ Q S hRp
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at key
    exact key.mpr h
  · rintro ⟨hRp, h⟩
    letI := hRp.isUnit.invertible
    refine ⟨hRp, ?_⟩
    have key := Matrix.PosDef.fromBlocks₂₂ Q S hRp
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at key
    exact key.mp h
