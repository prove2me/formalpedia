-- Prove2me | solution 1 for GlobalTheory.TeichPair.eq_zero_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:18.560157+00:00
-- url     : https://prove2.me/submissions/c2d8b69a-cbd7-4dde-80a4-356390e050c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.TeichPair
variable {C : Type} [Field C]
namespace GlobalTheory.TeichPair
theorem _root_.solution {V : VF C} {z : C} (h : ∀ N : ℕ, V.Ge N z) : z = 0 := by
  by_contra hz
  have h1 : V.v z ≠ ⊤ := fun h => hz (V.v.top_iff.1 h)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h1
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have := h N
  unfold VF.Ge at this
  rw [← ht] at this
  exact absurd (WithTop.coe_le_coe.1 this) (not_le.2 hN)
end GlobalTheory.TeichPair
