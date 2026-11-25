-- Prove2me | solution 1 for GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:22:17.277744+00:00
-- url     : https://prove2.me/submissions/2b26f46b-b9d1-47b2-9785-0f2947220586

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalOrthogonalRangeUnitarySelfReciprocal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalOrthogonalRangeUnitarySelfReciprocalStatement
import Theorems.Thm_GlobalTheory_csr_ker_orth_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 → ∀ (Q : K[X]), C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse → ∀ (x z : Fin n → K), aeval γ Q *ᵥ x = 0 → ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 := by
  first | exact @GlobalTheory.csr_ker_orth_range | exact GlobalTheory.csr_ker_orth_range | (intros; apply GlobalTheory.csr_ker_orth_range <;> assumption)
end _root_.GlobalTheory.T
