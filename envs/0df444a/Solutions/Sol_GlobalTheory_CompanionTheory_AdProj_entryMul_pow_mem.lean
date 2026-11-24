-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdProj.entryMul_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:29.825436+00:00
-- url     : https://prove2.me/submissions/bb945d3d-27c6-425f-a8a7-05b673bbd023

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
import Theorems.Thm_GlobalTheory_CompanionTheory_AdProj_diagonal_commutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdProj
namespace GlobalTheory.CompanionTheory.AdProj
theorem _root_.solution {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (k : ℕ) :
    entryMul h (fun t => t ^ k) X ∈ 𝔤 := by
  induction k with
  | zero =>
    have h0 : entryMul h (fun t => t ^ 0) X = X := by
      ext i j
      simp [entryMul]
    rw [h0]
    exact hX
  | succ k ih =>
    have hs : entryMul h (fun t => t ^ (k + 1)) X =
        Matrix.diagonal (fun i => (h i : ℂ)) * entryMul h (fun t => t ^ k) X -
          entryMul h (fun t => t ^ k) X * Matrix.diagonal (fun i => (h i : ℂ)) := by
      rw [diagonal_commutator]
      ext i j
      simp only [entryMul, Matrix.of_apply]
      push_cast
      ring
    rw [hs]
    exact hbr _ hD _ ih
end GlobalTheory.CompanionTheory.AdProj
