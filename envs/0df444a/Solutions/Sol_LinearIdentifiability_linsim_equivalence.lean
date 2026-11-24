-- Prove2me | solution 1 for LinearIdentifiability.linsim_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T09:12:58.483802+00:00
-- url     : https://prove2.me/submissions/d76b8ba1-68cb-41ce-9160-a9318207fee3

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix
namespace LinearIdentifiability


theorem linsim_equivalence {Θ X Y : Type*} {M : ℕ}
    (f : Θ → X → Fin M → ℝ) (g : Θ → Y → Fin M → ℝ) :
    Equivalence (LinSim f g) := by
  constructor
  · intro θ
    exact ⟨1, 1, by simp, by simp, fun x => by simp, fun y => by simp⟩
  · rintro θ₁ θ₂ ⟨A, B, hA, hB, hf, hg⟩
    exact ⟨A⁻¹, B⁻¹, Matrix.isUnit_nonsing_inv_det A hA, Matrix.isUnit_nonsing_inv_det B hB,
      fun x => by rw [hf x, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec],
      fun y => by rw [hg y, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hB, Matrix.one_mulVec]⟩
  · rintro θ₁ θ₂ θ₃ ⟨A, B, hA, hB, hf, hg⟩ ⟨A', B', hA', hB', hf', hg'⟩
    exact ⟨A * A', B * B', by rw [Matrix.det_mul]; exact hA.mul hA',
      by rw [Matrix.det_mul]; exact hB.mul hB',
      fun x => by rw [hf x, hf' x, Matrix.mulVec_mulVec], fun y => by rw [hg y, hg' y, Matrix.mulVec_mulVec]⟩

end LinearIdentifiability

open LinearIdentifiability in
theorem solution {Θ X Y : Type*} {M : ℕ}
    (f : Θ → X → Fin M → ℝ) (g : Θ → Y → Fin M → ℝ) :
    Equivalence (LinSim f g) := by
  constructor
  · intro θ
    exact ⟨1, 1, by simp, by simp, fun x => by simp, fun y => by simp⟩
  · rintro θ₁ θ₂ ⟨A, B, hA, hB, hf, hg⟩
    exact ⟨A⁻¹, B⁻¹, Matrix.isUnit_nonsing_inv_det A hA, Matrix.isUnit_nonsing_inv_det B hB,
      fun x => by rw [hf x, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec],
      fun y => by rw [hg y, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hB, Matrix.one_mulVec]⟩
  · rintro θ₁ θ₂ θ₃ ⟨A, B, hA, hB, hf, hg⟩ ⟨A', B', hA', hB', hf', hg'⟩
    exact ⟨A * A', B * B', by rw [Matrix.det_mul]; exact hA.mul hA',
      by rw [Matrix.det_mul]; exact hB.mul hB',
      fun x => by rw [hf x, hf' x, Matrix.mulVec_mulVec], fun y => by rw [hg y, hg' y, Matrix.mulVec_mulVec]⟩
