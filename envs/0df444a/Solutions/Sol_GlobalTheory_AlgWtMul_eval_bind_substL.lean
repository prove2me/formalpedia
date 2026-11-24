-- Prove2me | solution 1 for GlobalTheory.AlgWtMul.eval_bind_substL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:57:36.908522+00:00
-- url     : https://prove2.me/submissions/8d02b2f9-35f1-43a1-b40f-2fae1ce8e0c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
noncomputable section
open GlobalTheory GlobalTheory.AlgWtMul
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
namespace GlobalTheory.AlgWtMul
theorem _root_.solution (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q) =
      MvPolynomial.eval (upt (fun σ => A σ * Y σ)) Q := by
  calc MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt Y) (substL A v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt Y) (substL A v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt Y) (substL A v)) = upt (fun σ => A σ * Y σ) := by
        funext v
        simp [substL, upt, Matrix.mul_apply]
      rw [hf]
end GlobalTheory.AlgWtMul
