-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.isPolyRep_evPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:08.853624+00:00
-- url     : https://prove2.me/submissions/b47bec57-f782-40b9-9e4a-c6ba9b177cd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanRationalPointOrbitAlgebraicWeightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolynomialRepGLComplexAlgebraicWeightEvalPoint
import Theorems.Thm_GlobalTheory_AlgWtHW_tauPt_one
import Theorems.Thm_GlobalTheory_AlgWtHW_tauPt_mul
import Theorems.Thm_GlobalTheory_AlgWtHW_eval_evPt
import Theorems.Thm_GlobalTheory_AlgWtHW_evPt_eq_upt
import Theorems.Thm_GlobalTheory_AlgWtHW_isUPt_tauPt
import Theorems.Thm_GlobalTheory_T_algebraicWeight_polyMatrix_multiplicative


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
theorem _root_.solution (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type)
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (h : Agrees a b P) (τ : L →+* ℂ) :
    IsPolyRep (fun B => evM P (evPt τ B)) := by
  obtain ⟨h1, hm⟩ := GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n a ι b P h
  refine ⟨?_, ?_, ?_⟩
  · show evM P (evPt τ 1) = 1
    rw [evPt_eq_upt, tauPt_one]
    exact h1
  · intro A B
    show evM P (evPt τ (A * B)) = evM P (evPt τ A) * evM P (evPt τ B)
    rw [evPt_eq_upt, evPt_eq_upt, evPt_eq_upt, tauPt_mul]
    exact hm _ _ (isUPt_tauPt τ A) (isUPt_tauPt τ B)
  · intro i j
    refine ⟨MvPolynomial.bind₁ (tauSubst τ) (P i j), fun B => ?_⟩
    show MvPolynomial.eval (evPt τ B) (P i j) = _
    exact eval_evPt τ (P i j) B
end GlobalTheory.AlgWtHW
