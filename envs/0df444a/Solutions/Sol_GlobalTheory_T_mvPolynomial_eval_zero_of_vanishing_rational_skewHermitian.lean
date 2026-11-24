-- Prove2me | solution 1 for GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:33.929033+00:00
-- url     : https://prove2.me/submissions/2390c6ca-35b7-45c8-9044-91ae0268c393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
import Theorems.Thm_GlobalTheory_AlgWtHW_eval_upt_eq_zero_of_skew


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
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → MvPolynomial.eval (upt (ratPt S)) Q = 0) → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) → MvPolynomial.eval (upt Y) Q = 0 := by
  first | exact @GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew | exact GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew | (intros; apply GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew <;> assumption)
end _root_.GlobalTheory.T
