-- Prove2me | solution 1 for LowRankDenoise432.OptimalProjector.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:34:05.065979+00:00
-- url     : https://prove2.me/submissions/f7255800-3354-444d-93cf-787192b6afa3

import Mathlib
import Definitions.Def_LowRankDenoise432_OptimalProjector_Model

section
set_option autoImplicit false

open Matrix LowRankDenoise432.OptimalProjector

namespace LowRankDenoise432.Dev.L32

theorem sqNorm_eq_dot {d : ℕ} (v : Fin d → ℝ) : sqNorm v = v ⬝ᵥ v := by
  simp [sqNorm, dotProduct, sq]

end LowRankDenoise432.Dev.L32

namespace LowRankDenoise432.OptimalProjector

theorem chk_lemma_3_2 {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsOrthProjector Q)
    (c' c εbar : Fin d → ℝ) :
    projEstimate Q c' (c + εbar) - c = Q *ᵥ εbar - (1 - Q) *ᵥ (c - c') ∧
      sqNorm (projEstimate Q c' (c + εbar) - c) =
        sqNorm (Q *ᵥ εbar) + sqNorm ((1 - Q) *ᵥ (c - c')) := by
  have h1 : projEstimate Q c' (c + εbar) - c = Q *ᵥ εbar - (1 - Q) *ᵥ (c - c') := by
    unfold projEstimate
    have : c + εbar - c' = (c - c') + εbar := by abel
    rw [this, Matrix.mulVec_add, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  refine ⟨h1, ?_⟩
  rw [h1]
  obtain ⟨hs, hi⟩ := hQ
  -- cross term vanishes
  have hcross : (Q *ᵥ εbar) ⬝ᵥ ((1 - Q) *ᵥ (c - c')) = 0 := by
    have hQ1 : Q *ᵥ εbar = εbar ᵥ* Q := by
      rw [← Matrix.vecMul_transpose, hs]
    have hz : Q * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hi, sub_self]
    rw [hQ1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hz, Matrix.vecMul_zero, zero_dotProduct]
  simp only [LowRankDenoise432.Dev.L32.sqNorm_eq_dot]
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm ((1 - Q) *ᵥ (c - c')) (Q *ᵥ εbar), hcross]
  ring

end LowRankDenoise432.OptimalProjector
end

theorem solution : type_of% @LowRankDenoise432.OptimalProjector.chk_lemma_3_2 := @LowRankDenoise432.OptimalProjector.chk_lemma_3_2
