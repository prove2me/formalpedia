-- Prove2me | solution 1 for GlobalTheory.exists_norm_pow_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:47.718811+00:00
-- url     : https://prove2.me/submissions/5327ff67-421e-4316-aa8d-f887137a7594

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {C : Type*} [NormedField C] [IsAlgClosed C] (x : C)
    {n : ℕ} (hn : 0 < n) : ∃ y : C, ‖y‖ ^ n = ‖x‖ := by
  obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq x hn
  exact ⟨y, (norm_pow y n).symm⟩
end GlobalTheory
