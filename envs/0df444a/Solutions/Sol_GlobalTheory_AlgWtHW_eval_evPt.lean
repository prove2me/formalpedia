-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.eval_evPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:38.931485+00:00
-- url     : https://prove2.me/submissions/51f90d3c-d21d-4eca-9d29-08190d714100

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
theorem _root_.solution (τ : L →+* ℂ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (B : GL (Fin n) ℂ) :
    MvPolynomial.eval (evPt τ B) Q =
      MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2))
        (MvPolynomial.bind₁ (tauSubst τ) Q) := by
  have e := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ)
    (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) (tauSubst τ) Q
  erw [e]
  show MvPolynomial.eval _ Q = MvPolynomial.eval _ Q
  congr 2
  funext p
  simp only [evPt, tauSubst]
  split_ifs <;> simp [Matrix.one_apply, *]
end GlobalTheory.AlgWtHW
