-- Prove2me | solution 1 for GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:06.902797+00:00
-- url     : https://prove2.me/submissions/96639f67-3c06-436f-ac99-189ed6b87b0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPoints
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPointsStatement
import Theorems.Thm_GlobalTheory_UDense_eval_eq_zero_of_rat


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
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) → ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by
  first | exact @GlobalTheory.UDense.eval_eq_zero_of_rat | exact GlobalTheory.UDense.eval_eq_zero_of_rat | (intros; apply GlobalTheory.UDense.eval_eq_zero_of_rat <;> assumption)
end _root_.GlobalTheory.T
