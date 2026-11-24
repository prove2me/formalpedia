-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.tauPt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:43.968977+00:00
-- url     : https://prove2.me/submissions/81e4ef1f-5399-45cb-8922-b2b7da36220c

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
theorem _root_.solution (τ : L →+* ℂ) : tauPt τ (1 : GL (Fin n) ℂ) = fun _ => 1 := by
  funext σ
  simp only [tauPt, inv_one, Units.val_one, Matrix.transpose_one]
  split_ifs <;> rfl
end GlobalTheory.AlgWtHW
