-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.tauPt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:43.117488+00:00
-- url     : https://prove2.me/submissions/4d12e587-f6a0-4b4d-86a3-3ec4f65ca103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanRationalPointOrbitAlgebraicWeightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolynomialRepGLComplexAlgebraicWeightEvalPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
namespace GlobalTheory.AlgWtHW
theorem _root_.solution (τ : L →+* ℂ) (A B : GL (Fin n) ℂ) :
    tauPt τ (A * B) = fun σ => tauPt τ A σ * tauPt τ B σ := by
  funext σ
  simp only [tauPt]
  split_ifs
  · simp
  · simp [_root_.mul_inv_rev, Matrix.transpose_mul]
  · simp
end GlobalTheory.AlgWtHW
