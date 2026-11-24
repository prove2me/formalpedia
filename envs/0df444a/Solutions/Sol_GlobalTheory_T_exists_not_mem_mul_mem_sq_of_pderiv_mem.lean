-- Prove2me | solution 1 for GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:05.20648+00:00
-- url     : https://prove2.me/submissions/ab3b4075-b73a-4fbd-b5ce-d25f4f5dfd3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMemStatement
import Theorems.Thm_GlobalTheory_mem_sq_localization_of_pderiv_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  first | exact @GlobalTheory.mem_sq_localization_of_pderiv_mem | exact GlobalTheory.mem_sq_localization_of_pderiv_mem | (intros; apply GlobalTheory.mem_sq_localization_of_pderiv_mem <;> assumption)
end _root_.GlobalTheory.T
