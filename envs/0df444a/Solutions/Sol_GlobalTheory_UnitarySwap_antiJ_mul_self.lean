-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.antiJ_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:49:43.459352+00:00
-- url     : https://prove2.me/submissions/7e0f10cf-8182-48e6-9be4-47778bd43fcb

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
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
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · have := i.2
    have := j.2
    simp only [antiJ, Fin.val_rev, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · intro b _ hb
    have : ¬ (i.val + b.val + 1 = n) := fun h => hb (Fin.ext (by rw [Fin.val_rev]; omega))
    simp [antiJ, this]
  · simp
end GlobalTheory.UnitarySwap
