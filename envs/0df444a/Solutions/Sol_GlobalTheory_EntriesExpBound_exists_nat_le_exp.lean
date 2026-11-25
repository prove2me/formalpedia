-- Prove2me | solution 1 for GlobalTheory.EntriesExpBound.exists_nat_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:24.396797+00:00
-- url     : https://prove2.me/submissions/91afc130-16a9-482d-bf00-624647ab4ab5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEntriesLeExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EntriesExpBound
namespace GlobalTheory.EntriesExpBound
theorem _root_.solution (x : WithZero (Multiplicative ℤ)) :
    ∃ k : ℕ, x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log x).toNat, ?_⟩
    calc x = WithZero.exp (WithZero.log x) := (WithZero.exp_log hx).symm
      _ ≤ _ := WithZero.exp_le_exp.mpr (Int.self_le_toNat _)
end GlobalTheory.EntriesExpBound
