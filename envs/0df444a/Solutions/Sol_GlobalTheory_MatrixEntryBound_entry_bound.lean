-- Prove2me | solution 1 for GlobalTheory.MatrixEntryBound.entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:54:37.0678+00:00
-- url     : https://prove2.me/submissions/705bab5c-e53b-443b-8b8e-62d4dc95b5bb

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.MatrixEntryBound
namespace GlobalTheory.MatrixEntryBound
theorem _root_.solution {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L}
    (hϖ : (Valued.v : L → WithZero (Multiplicative ℤ)) ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ ^ m * x) ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by simp [hx]⟩
  · have hv : (Valued.v : L → WithZero (Multiplicative ℤ)) x ≠ 0 := by
      simpa using hx
    refine ⟨(WithZero.log (Valued.v x)).toNat, fun m hm => ?_⟩
    rw [map_mul, map_pow, hϖ, ← WithZero.exp_log hv, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    have : WithZero.log (Valued.v x) ≤ (m : ℤ) := by
      have := Int.self_le_toNat (WithZero.log (Valued.v x)); omega
    simp; omega
end GlobalTheory.MatrixEntryBound
