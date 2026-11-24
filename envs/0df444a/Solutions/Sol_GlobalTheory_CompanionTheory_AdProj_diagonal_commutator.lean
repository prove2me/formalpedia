-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdProj.diagonal_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:09.032054+00:00
-- url     : https://prove2.me/submissions/0d3ffcf4-f88c-4b93-ba37-43adfbfae3be

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus

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
theorem _root_.solution {n : ℕ} (h : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.diagonal (fun i => (h i : ℂ)) * X - X * Matrix.diagonal (fun i => (h i : ℂ))
      = entryMul h (fun t => t) X := by
  ext i j
  simp only [entryMul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  push_cast
  ring
end GlobalTheory.CompanionTheory.AdProj
