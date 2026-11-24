-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.form_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:31.596432+00:00
-- url     : https://prove2.me/submissions/f9d15c36-d7f9-4979-8e86-d7ab6621ad0f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_form_apply
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
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.UnitarySwap
theorem _root_.solution (J M : Matrix (Fin n) (Fin n) L) (u v : Fin n → L) :
    form σ J (M *ᵥ u) (M *ᵥ v) = form σ (cT σ M * J * M) u v := by
  have : σ ∘ (M *ᵥ u) = (σ ∘ u) ᵥ* cT σ M := by
    funext i
    simp [cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [form_apply, form_apply, this, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
end GlobalTheory.UnitarySwap
