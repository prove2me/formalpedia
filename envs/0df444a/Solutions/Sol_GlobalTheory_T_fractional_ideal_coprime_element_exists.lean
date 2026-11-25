-- Prove2me | solution 1 for GlobalTheory.T.fractional_ideal_coprime_element_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:17:46.686822+00:00
-- url     : https://prove2.me/submissions/c5e60b16-a5d5-457e-9afe-62ed2793e81a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealCoprimeElementExists
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealCoprimeElementExistsStatement
import Theorems.Thm_GlobalTheory_exists_mem_spanSingleton_mul_inv_add_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [NumberField F] (Y N : FractionalIdeal (𝓞 F)⁰ F), Y ≠ 0 → N ≠ 0 → N ≤ 1 →
    ∃ β ∈ Y, FractionalIdeal.spanSingleton (𝓞 F)⁰ β * Y⁻¹ + N = 1 := by
  first | exact @GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one | exact GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one | (intros; apply GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one <;> assumption)
end _root_.GlobalTheory.T
