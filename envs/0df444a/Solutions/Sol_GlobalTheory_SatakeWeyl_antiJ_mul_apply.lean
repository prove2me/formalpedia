-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.antiJ_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:23.001786+00:00
-- url     : https://prove2.me/submissions/2873cd4f-8390-4f5b-aa50-dadc25ee7124

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
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
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (antiJ L n * M) i j = M i.rev j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · have : i.val + i.rev.val + 1 = n := by have := i.2; rw [Fin.val_rev]; omega
    simp only [antiJ, this, if_true, one_mul]
  · intro b _ hb
    have : ¬ (i.val + b.val + 1 = n) := fun h => hb (Fin.ext (by rw [Fin.val_rev]; omega))
    simp [antiJ, this]
  · simp
end GlobalTheory.SatakeWeyl
