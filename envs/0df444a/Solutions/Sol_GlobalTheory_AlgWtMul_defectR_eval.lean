-- Prove2me | solution 1 for GlobalTheory.AlgWtMul.defectR_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:07.927887+00:00
-- url     : https://prove2.me/submissions/3fffc2da-a39c-49ff-a3d7-4e47e4a9007d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicative
import Theorems.Thm_GlobalTheory_AlgWtMul_eval_bind_substR

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
theorem _root_.solution {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) (P i j) -
        ∑ m, P i m * MvPolynomial.C (evM P (upt B) m j)) =
      evM P (upt (fun σ => X σ * B σ)) i j - (evM P (upt X) * evM P (upt B)) i j := by
  rw [map_sub, eval_bind_substR]
  simp [evM, Matrix.mul_apply]
end GlobalTheory.AlgWtMul
