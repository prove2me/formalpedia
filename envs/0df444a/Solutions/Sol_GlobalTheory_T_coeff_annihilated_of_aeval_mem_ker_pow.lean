-- Prove2me | solution 1 for GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:07.949627+00:00
-- url     : https://prove2.me/submissions/b2d3b1b7-a49e-4e0b-b73d-6623b3a975f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPowStatement
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_exists_mul_coeff_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d N : ℕ), ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) → (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → MvPolynomial.coeff α P = 0) → MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * MvPolynomial.coeff α P = 0 := by
  first | exact @GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | exact GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | (intros; apply GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero <;> assumption)
end _root_.GlobalTheory.T
