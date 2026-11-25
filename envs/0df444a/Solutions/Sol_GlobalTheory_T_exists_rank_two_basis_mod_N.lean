-- Prove2me | solution 1 for GlobalTheory.T.exists_rank_two_basis_mod_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:20:31.516701+00:00
-- url     : https://prove2.me/submissions/89a478a9-e90f-4fe9-aca1-e998e2a6761a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankTwoBasisModN
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankTwoBasisModNStatement
import Theorems.Thm_GlobalTheory_LatticeModN_exists_gen_modN


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M], Module.finrank ℤ M = 2 * Module.finrank ℚ F → ∀ N : ℕ, 1 ≤ N → ∃ x : Fin 2 → M, (∀ m : M, ∃ (a b : 𝓞 F) (m' : M), m = a • x 0 + b • x 1 + N • m') ∧ ∀ a b : 𝓞 F, (∃ m' : M, a • x 0 + b • x 1 = N • m') → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  first | exact @GlobalTheory.LatticeModN.exists_gen_modN | exact GlobalTheory.LatticeModN.exists_gen_modN | (intros; apply GlobalTheory.LatticeModN.exists_gen_modN <;> assumption)
end _root_.GlobalTheory.T
