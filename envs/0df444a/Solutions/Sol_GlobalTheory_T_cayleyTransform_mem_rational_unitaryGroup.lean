-- Prove2me | solution 1 for GlobalTheory.T.cayleyTransform_mem_rational_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:04:16.016165+00:00
-- url     : https://prove2.me/submissions/b359fdea-b76f-4aeb-b4dd-97b8de0421da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroupStatement
import Theorems.Thm_GlobalTheory_CayleyRat_exists_mem_GQ0_eq_cayley_of_skew_hermitian


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
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  first | exact @GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | exact GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | (intros; apply GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian <;> assumption)
end _root_.GlobalTheory.T
