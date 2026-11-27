-- Prove2me | solution 1 for GlobalTheory.T.tsum_inv_card_stabilizer_eq_tsum_mul_card_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:48.412516+00:00
-- url     : https://prove2.me/submissions/0cb4d8e1-a671-45e9-ac8a-d1139bd3f721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiber
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiberStatement
import Theorems.Thm_GlobalTheory_tsum_inv_stabilizer_eq_tsum_mul_fiber


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y] (π : L → Y), (∀ (g : Γ) (x : L), π (g • x) = g • π x) → (∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) → (∑' o : MulAction.orbitRel.Quotient Γ L, (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹) = ∑' o : MulAction.orbitRel.Quotient Γ Y, (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹ * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by
  first | exact @GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber | exact GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber | (intros; apply GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber <;> assumption)
end _root_.GlobalTheory.T
