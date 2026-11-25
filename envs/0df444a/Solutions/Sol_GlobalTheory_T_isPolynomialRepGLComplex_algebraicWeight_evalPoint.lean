-- Prove2me | solution 1 for GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:20:37.104851+00:00
-- url     : https://prove2.me/submissions/bae39df0-7790-4cb4-99fc-e957529afd23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolynomialRepGLComplexAlgebraicWeightEvalPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanRationalPointOrbitAlgebraicWeightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Theorems.Thm_GlobalTheory_AlgWtHW_isPolyRep_evPt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ τ : L →+* ℂ, IsPolyRep (fun B => evM P (evPt τ B)) := by
  first | exact @GlobalTheory.AlgWtHW.isPolyRep_evPt | exact GlobalTheory.AlgWtHW.isPolyRep_evPt | (intros; apply GlobalTheory.AlgWtHW.isPolyRep_evPt <;> assumption)
end _root_.GlobalTheory.T
