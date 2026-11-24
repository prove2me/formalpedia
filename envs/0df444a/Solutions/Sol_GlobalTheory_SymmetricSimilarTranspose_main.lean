-- Prove2me | solution 1 for GlobalTheory.SymmetricSimilarTranspose.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:58.860082+00:00
-- url     : https://prove2.me/submissions/1d3aad29-de01-4893-a24f-a44002e90629

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBilinCyclic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhaus
import Theorems.Thm_GlobalTheory_SymmetricSimilarTranspose_exists_bilin
import Theorems.Thm_GlobalTheory_SimilarTranspose_exists_bilin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SymmetricSimilarTranspose
namespace GlobalTheory.SymmetricSimilarTranspose
theorem _root_.solution : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P.transpose = P ∧ P * A = A.transpose * P := by
  intro k ι _ _ _ A
  obtain ⟨B, h1, h2, h3⟩ := exists_bilin (Matrix.toLin' A)
  obtain ⟨P, rfl⟩ := (Matrix.toBilin' (R₁ := k) (n := ι)).surjective B
  simp only [Matrix.toBilin'_apply', Matrix.toLin'_apply] at h1 h2 h3
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    refine (injective_iff_map_eq_zero P.mulVecLin).mpr fun y hy => h2 y fun x => ?_
    rw [Matrix.mulVecLin_apply] at hy
    rw [hy, dotProduct_zero]
  · ext i j
    have := h3 (Pi.single j 1) (Pi.single i 1)
    simpa using this
  · apply (Matrix.toBilin' (R₁ := k) (n := ι)).injective
    refine LinearMap.ext₂ fun x y => ?_
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec, ← h1,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]
end GlobalTheory.SymmetricSimilarTranspose
