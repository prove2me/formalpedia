-- Prove2me | solution 1 for GlobalTheory.AlgWtMul.defectL_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:33.898796+00:00
-- url     : https://prove2.me/submissions/20fd05ee-a0cd-4932-ae4c-2dafd0849c0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicative
import Theorems.Thm_GlobalTheory_AlgWtMul_eval_bind_substL

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
    (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt A) i m) * P m j) =
      evM P (upt (fun σ => A σ * Y σ)) i j - (evM P (upt A) * evM P (upt Y)) i j := by
  rw [map_sub, eval_bind_substL]
  simp [evM, Matrix.mul_apply]
end GlobalTheory.AlgWtMul
