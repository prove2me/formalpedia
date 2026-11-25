-- Prove2me | solution 1 for GlobalTheory.hhJ_self_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:17.810698+00:00
-- url     : https://prove2.me/submissions/a1d156ba-838a-4fd4-b515-f3502948b5c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormHhJSelfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (ε : Fin n → Bool) (x : Fin n → M) :
    (hhJ ε x x).im = 0 := by
  unfold hhJ
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h : (⟪x c, x c⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (x c)
  split_ifs <;> simp [-inner_self_eq_norm_sq_to_K, h]
end GlobalTheory
