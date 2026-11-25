-- Prove2me | solution 1 for GlobalTheory.T.exists_eq_nsmul_of_forall_char_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:24.573542+00:00
-- url     : https://prove2.me/submissions/59ded798-cff9-4bf3-89c1-5a6540c3d855

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSmulOfForallCharPowEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSmulOfForallCharPowEqOneStatement
import Theorems.Thm_GlobalTheory_mem_smul_of_forall_char_pow_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F] [IsAlgClosed F] (k : ℕ), (k : F) ≠ 0 → ∀ d : X, (∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd d) = 1) → ∃ z : X, d = k • z := by
  first | exact @GlobalTheory.mem_smul_of_forall_char_pow_eq_one | exact GlobalTheory.mem_smul_of_forall_char_pow_eq_one | (intros; apply GlobalTheory.mem_smul_of_forall_char_pow_eq_one <;> assumption)
end _root_.GlobalTheory.T
