-- Prove2me | solution 1 for GlobalTheory.hhJ_self_norm_le_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:19.903026+00:00
-- url     : https://prove2.me/submissions/d434157f-3396-4378-a8c9-1957543c7b01

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
    ‖hhJ ε x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  unfold hhJ
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, inner_self_eq_norm_sq_to_K]
  split_ifs <;> simp
end GlobalTheory
